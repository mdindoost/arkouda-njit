module BFSMsg {
    // Chapel modules.
    use IO;
    use Reflection;
    use Set;
    use Time; 
    use Sort;
    use List;
    use CommDiagnostics;
    use ReplicatedDist;

    // Package modules. 
    use DistributedBag;
    use CopyAggregation;
    
    // Arachne modules.
    use GraphArray;
    use Utils;
    use BuildGraphMsg;
    
    // Arkouda modules.
    use MultiTypeSymbolTable;
    use MultiTypeSymEntry;
    use CommAggregation;
    use ServerConfig;
    use ArgSortMsg;
    use AryUtil;
    use Logging;
    use Message;
    
    // Server message logger. 
    private config const logLevel = LogLevel.DEBUG;
    const smLogger = new Logger(logLevel);
    var outMsg:string;

    /**
    * Check if a particular value x is local in an array. It is local if it is between or equal to 
    * the low and high values passed. 
    *
    * x: value we are searching for. 
    * low: lower value of subdomain. 
    * high: higher value of subdomain. 
    *
    * returns: true if local, false otherwise. 
    */
    private proc xlocal(x: int, low: int, high: int):bool {
        return low <= x && x <= high;
    }

    /**
    * Check if a particular value x is remote in an array. It is remote if it is not between or 
    * equal to the low and high values passed. 
    *
    * x: value we are searching for. 
    * low: lower value of subdomain. 
    * high: higher value of subdomain. 
    *
    * returns: true if remote, false otherwise. 
    */
    private proc xremote(x: int, low: int, high: int):bool {
        return !xlocal(x, low, high);
    }

    // Declare our frontier queues here to be sets, done globally. 
    var D_util = {0..1} dmapped Replicated();
    var queues : [D_util] set(int, parSafe=true);
    var queueIdx : int;

    const dstBuffSize = getEnvInt("CHPL_AGGREGATION_DST_BUFF_SIZE", 4096);
    const yieldFrequency = getEnvInt("CHPL_AGGREGATION_YIELD_FREQUENCY", 1024);

    /**
    * Record for remote set aggregator to perform various parallel set additions when buffer
    * is full. Built from a combination of the Arkouda aggregator and Thomas Rolinger's 
    * aggregator.
    */
    record SetDstAggregator {
        type elemType;
        type aggType = elemType;
        const bufferSize = dstBuffSize;
        const myLocaleSpace = LocaleSpace;
        var opsUntilYield = yieldFrequency;
        var lBuffers: [myLocaleSpace] [0..#bufferSize] aggType;
        var rBuffers: [myLocaleSpace] remoteBuffer(aggType);
        var bufferIdxs: [myLocaleSpace] int;

        proc postinit() {
            for loc in myLocaleSpace {
                rBuffers[loc] = new remoteBuffer(aggType, bufferSize, loc);
            }
        }
    
        proc deinit() {
            flush();
        }

        proc flush() {
            for loc in myLocaleSpace {
                _flushBuffer(loc, bufferIdxs[loc], freeData=true);
            }
        }

        inline proc copy(const loc, const in srcVal: elemType) {
            // Get our current index into the buffer for dst's locale
            ref bufferIdx = bufferIdxs[loc];

            // Buffer the address and desired value
            lBuffers[loc][bufferIdx] = srcVal;
            bufferIdx += 1;

            // Flush our buffer if it's full. If it's been a while since we've let
            // other tasks run, yield so that we're not blocking remote tasks from
            // flushing their buffers.
            if bufferIdx == bufferSize {
                _flushBuffer(loc, bufferIdx, freeData=false);
                opsUntilYield = yieldFrequency;
            } else if opsUntilYield == 0 {
                chpl_task_yield();
                opsUntilYield = yieldFrequency;
            } else {
                opsUntilYield -= 1;
            }
        }

        proc _flushBuffer(loc: int, ref bufferIdx, freeData) {
            // Get the buffer id to extract the buffered info.
            const myBufferIdx = bufferIdx;
            if myBufferIdx == 0 then return;

            // Allocate a remote buffer
            ref rBuffer = rBuffers[loc];
            const remBufferPtr = rBuffer.cachedAlloc();

            // Copy local buffer to remote buffer
            rBuffer.PUT(lBuffers[loc], myBufferIdx);

            // Process remote buffer
            on Locales[loc] {
                ref q = queues[(queueIdx+1)%2];
                for srcVal in rBuffer.localIter(remBufferPtr, myBufferIdx) { /* forall gives error: A standalone or leader iterator is not found for the iterable expression in this forall loop */
                    q.add(srcVal);
                }
                if freeData {
                    rBuffer.localFree(remBufferPtr);
                }
            }
            if freeData {
                rBuffer.markFreed();
            }
            bufferIdx = 0;
        }
    } // end of SetDstAggregator

    /**
    * Run BFS on a(n) (un)directed and (un)weighted graph. 
    *
    * cmd: operation to perform. 
    * msgArgs: arugments passed to backend. 
    * SymTab: symbol table used for storage. 
    *
    * returns: message back to Python.
    */
    proc segBFSMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        var repMsg: string;
        var depthName:string;

        var n_verticesN = msgArgs.getValueOf("NumOfVertices");
        var n_edgesN = msgArgs.getValueOf("NumOfEdges");
        var directedN = msgArgs.getValueOf("Directed");
        var weightedN = msgArgs.getValueOf("Weighted");
        var graphEntryName = msgArgs.getValueOf("GraphName");

        var Nv = n_verticesN:int;
        var Ne = n_edgesN:int;
        var directed = directedN:int:bool;
        var weighted = weightedN:int:bool;
        var timer:stopwatch;

        var root:int; 
        var srcN, dstN, startN, neighborN, eweightN, rootN: string; 
        var srcRN, dstRN, startRN, neighborRN: string; 
        var gEntry: borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st); 
        var ag = gEntry.graph; 

        // Create empty depth array to return at the end of execution. 
        var depth = makeDistArray(Nv, int);
        depth = -1;

        /* Original method created by Zhihui Du using reversed arrays for undirected graphs. */
        proc bfs_kernel_und(nei: [?D1] int, start_i: [?D2] int, src: [?D3] int, dst: [?D4] int, 
                                neiR: [?D5] int, start_iR: [?D6] int, srcR: [?D7] int, 
                                dstR: [?D8] int):string throws {            
            depth = -1;
            var cur_level = 0;
            var current_frontier = new DistBag(int, Locales);
            var next_frontier = new DistBag(int, Locales);
            current_frontier.add(root);
            var size_current_frontier = 1 : int;
            depth[root] = cur_level;

            while (size_current_frontier > 0) { 
                coforall loc in Locales {
                    on loc {
                        var edgeBegin = src.localSubdomain().low;
                        var edgeEnd = src.localSubdomain().high;
                        var vertexBegin = src[edgeBegin];
                        var vertexEnd = src[edgeEnd];
                        var vertexBeginR = srcR[edgeBegin];
                        var vertexEndR = srcR[edgeEnd];

                        forall i in current_frontier {
                            if((xlocal(i, vertexBegin, vertexEnd))) { 
                                var numNF = nei[i];
                                var edgeId = start_i[i];
                                var nextStart = max(edgeId, edgeBegin);
                                var nextEnd = min(edgeEnd, edgeId + numNF - 1);
                                ref neighborhood = dst[nextStart..nextEnd];
                                forall j in neighborhood {
                                    if (depth[j] == -1) {
                                        depth[j] = cur_level + 1;
                                        next_frontier.add(j);
                                    }
                                }
                            } 
                            if ((xlocal(i, vertexBeginR, vertexEndR))) {
                                var numNF = neiR[i];
                                var edgeId = start_iR[i];
                                var nextStart = max(edgeId, edgeBegin);
                                var nextEnd = min(edgeEnd, edgeId + numNF - 1);
                                ref neighborhoodR = dstR[nextStart..nextEnd];
                                forall j in neighborhoodR {
                                    if (depth[j] == -1) {
                                        depth[j] = cur_level + 1;
                                        next_frontier.add(j);
                                    }
                                }
                            }
                        } //end forall
                    } // end on loc
                }// end coforall loc
                cur_level += 1;
                size_current_frontier = next_frontier.size;
                current_frontier <=> next_frontier;
                next_frontier.clear();
            }// end while 
            return "success";
        }// end of bfs_kernel_und

        /* Based off original method, butt concatenates neighborhood with neighborhood of reversed neighbors. */
        proc bfs_kernel_und_concatenate(nei: [?D1] int, start_i: [?D2] int, src: [?D3] int, dst: [?D4] int, 
                                neiR: [?D5] int, start_iR: [?D6] int, srcR: [?D7] int, 
                                dstR: [?D8] int):string throws {            
            depth = -1;
            var cur_level = 0;
            var current_frontier = new DistBag(int, Locales);
            var next_frontier = new DistBag(int, Locales);
            current_frontier.add(root);
            var size_current_frontier = 1 : int;
            depth[root] = cur_level;

            while (size_current_frontier > 0) { 
                coforall loc in Locales {
                    on loc {
                        var edgeBegin = src.localSubdomain().low;
                        var edgeEnd = src.localSubdomain().high;
                        var vertexBegin = src[edgeBegin];
                        var vertexEnd = src[edgeEnd];
                        var vertexBeginR = srcR[edgeBegin];
                        var vertexEndR = srcR[edgeEnd];

                        forall i in current_frontier {
                            var nextStart, nextEnd, nextStartR, nextEndR: int;
                            var reg, rev: bool = false;

                            if((xlocal(i, vertexBegin, vertexEnd))) { 
                                var numNF = nei[i];
                                var edgeId = start_i[i];
                                nextStart = max(edgeId, edgeBegin);
                                nextEnd = min(edgeEnd, edgeId + numNF - 1);
                                reg = true;
                            } 
                            if ((xlocal(i, vertexBeginR, vertexEndR))) {
                                var numNF = neiR[i];
                                var edgeId = start_iR[i];
                                nextStartR = max(edgeId, edgeBegin);
                                nextEndR = min(edgeEnd, edgeId + numNF - 1);
                                rev = true;
                            }

                            if(reg && rev) {
                                var neighborhood = dst[nextStart..nextEnd];
                                var neighborhoodR = dstR[nextStartR..nextEndR];
                                var full_neighborhood: [0..neighborhood.size+neighborhoodR.size-1] int;
                                
                                forall (i,j) in zip(0..neighborhood.size-1,neighborhood) {
                                    full_neighborhood[i] = j;
                                }

                                forall (i,j) in zip(neighborhood.size..neighborhood.size+neighborhoodR.size-1,neighborhoodR) {
                                    full_neighborhood[i] = j;
                                }
                            
                                forall j in full_neighborhood {
                                    if (depth[j] == -1) {
                                        depth[j] = cur_level + 1;
                                        next_frontier.add(j);
                                    }
                                }
                            } 

                            if (reg && !rev) {
                                ref neighborhood = dst[nextStart..nextEnd];
                                forall j in neighborhood {
                                    if (depth[j] == -1) {
                                        depth[j] = cur_level + 1;
                                        next_frontier.add(j);
                                    }
                                }
                            }
                            
                            if (!reg && rev) {
                                ref neighborhoodR = dstR[nextStartR..nextEndR];
                                forall j in neighborhoodR {
                                    if (depth[j] == -1) {
                                        depth[j] = cur_level + 1;
                                        next_frontier.add(j);
                                    }
                                }
                            }
                        } //end forall
                    } // end on loc
                }// end coforall loc
                cur_level += 1;
                size_current_frontier = next_frontier.size;
                current_frontier <=> next_frontier;
                next_frontier.clear();
            }// end while 
            return "success";
        }// end of bfs_kernel_und_concatenate

        /* Same as original but places the if statements together into a cobegin statement to spawn them
         * at the same time. */
        proc bfs_kernel_und_cobegin(nei: [?D1] int, start_i: [?D2] int, src: [?D3] int, dst: [?D4] int, 
                                neiR: [?D5] int, start_iR: [?D6] int, srcR: [?D7] int, 
                                dstR: [?D8] int):string throws {            
            depth = -1;
            var cur_level = 0;
            var current_frontier = new DistBag(int, Locales);
            var next_frontier = new DistBag(int, Locales);
            current_frontier.add(root);
            var size_current_frontier = 1 : int;
            depth[root] = cur_level;

            while (size_current_frontier > 0) { 
                coforall loc in Locales {
                    on loc {
                        var edgeBegin = src.localSubdomain().low;
                        var edgeEnd = src.localSubdomain().high;
                        var vertexBegin = src[edgeBegin];
                        var vertexEnd = src[edgeEnd];
                        var vertexBeginR = srcR[edgeBegin];
                        var vertexEndR = srcR[edgeEnd];

                        forall i in current_frontier {
                            cobegin {
                                if((xlocal(i, vertexBegin, vertexEnd))) { 
                                    var numNF = nei[i];
                                    var edgeId = start_i[i];
                                    var nextStart = max(edgeId, edgeBegin);
                                    var nextEnd = min(edgeEnd, edgeId + numNF - 1);
                                    // num_local_reg[here.id].add(1);
                                    ref neighborhood = dst[nextStart..nextEnd];
                                    forall j in neighborhood {
                                        if (depth[j] == -1) {
                                            depth[j] = cur_level + 1;
                                            next_frontier.add(j);
                                        }
                                    }
                                } 
                                if ((xlocal(i, vertexBeginR, vertexEndR))) {
                                    var numNF = neiR[i];
                                    var edgeId = start_iR[i];
                                    var nextStart = max(edgeId, edgeBegin);
                                    var nextEnd = min(edgeEnd, edgeId + numNF - 1);
                                    // num_local_rev[here.id].add(1);
                                    ref neighborhoodR = dstR[nextStart..nextEnd];
                                    forall j in neighborhoodR {
                                        if (depth[j] == -1) {
                                            depth[j] = cur_level + 1;
                                            next_frontier.add(j);
                                        }
                                    }
                                }
                            }
                        } //end forall
                    } // end on loc
                }// end coforall loc
                cur_level += 1;
                size_current_frontier = next_frontier.size;
                current_frontier <=> next_frontier;
                next_frontier.clear();
            }// end while 
            return "success";
        }// end of bfs_kernel_und_cobegin

        /* BUILD A VERTEX-PARTITIONED GRAPH TO STORE NEIGHBORHOODS FULLY ON ONE NODE */
        var NEI = toSymEntry(ag.getComp("NEIGHBOR"), int).a;
        var START_I = toSymEntry(ag.getComp("START_IDX"), int).a;
        var SRC = toSymEntry(ag.getComp("SRC"), int).a;
        var DST = toSymEntry(ag.getComp("DST"), int).a;
        var NEIR = toSymEntry(ag.getComp("NEIGHBOR_R"), int).a;
        var START_IR = toSymEntry(ag.getComp("START_IDX_R"), int).a;
        var SRCR = toSymEntry(ag.getComp("SRC_R"), int).a;
        var DSTR = toSymEntry(ag.getComp("DST_R"), int).a;

        var neighbor_complete: [NEI.domain] list(int, parSafe=true);
        
        forall u in NEI.domain {
            var start = START_I[u];
            var end = start + NEI[u];

            ref neighborhood = DST[start..<end];

            forall v in neighborhood {
                neighbor_complete[u].append(v);
            }
        }

        forall u in NEIR.domain {
            var start = START_IR[u];
            var end = start + NEIR[u];

            ref neighborhoodR = DSTR[start..<end];

            forall v in neighborhoodR {
                neighbor_complete[u].append(v);
            }
        }

        /* MERGE REVERSED ARRAYS INTO REGULAR ARRAYS */
        var SRC_COMPLETE = makeDistArray(SRC.size + DST.size, int);
        var DST_COMPLETE: [SRC_COMPLETE.domain] int;
        
        // forall i in SRC.domain { 
        //     SRC_COMPLETE[i] = SRC[i];
        //     DST_COMPLETE[i] = DST[i];
        // }
        SRC_COMPLETE[SRC.domain] = SRC;
        DST_COMPLETE[SRC.domain] = DST;

        // var final_i_start = SRC.size;
        // var final_i_end = final_i_start + SRC.size;
        // for (i,j) in zip(final_i_start..final_i_end, SRC.domain) {
        //     SRC_COMPLETE[i] = DST[j];
        //     DST_COMPLETE[i] = SRC[j];
        // }
        SRC_COMPLETE[SRC.size..] = DST;
        DST_COMPLETE[SRC.size..] = SRC;


        var e_weight: [SRC_COMPLETE.domain] real;
        combine_sort(SRC_COMPLETE, DST_COMPLETE, e_weight, false, false);

        var nv = new set(int, parSafe=true);
        forall u in SRC_COMPLETE with (ref nv) {
            nv.add(u);
        }
        var NEI_COMPLETE = makeDistArray(nv.size, int);
        var START_I_COMPLETE: [NEI_COMPLETE.domain] int;
        
        writeln("SRC SIZE = ", SRC.size);
        writeln("SRCR SIZE = ", SRCR.size);
        writeln("SRC_COMPLETE SIZE = ", SRC_COMPLETE.size);
        writeln("NEI SIZE = ", NEI.size);
        writeln("START_I_COMPLETE SIZE = ", START_I_COMPLETE.size);
        writeln("NEI_COMPLETE SIZE = ", NEI_COMPLETE.size);

        set_neighbor(SRC_COMPLETE, START_I_COMPLETE, NEI_COMPLETE);

        /* Full neighborhoods are stored in an adjacency list and assembled only once. */
        proc bfs_kernel_und_adj_list(nei: [?D1] int, start_i: [?D2] int, src: [?D3] int, dst: [?D4] int, 
                                neiR: [?D5] int, start_iR: [?D6] int, srcR: [?D7] int, 
                                dstR: [?D8] int):string throws {            
            depth = -1;
            var cur_level = 0;
            var current_frontier = new DistBag(int, Locales);
            var next_frontier = new DistBag(int, Locales);
            current_frontier.add(root);
            var size_current_frontier = 1 : int;
            depth[root] = cur_level;

            while (size_current_frontier > 0) { 
                coforall loc in Locales {
                    on loc {
                        var vertexBegin = nei.localSubdomain().low;
                        var vertexEnd = nei.localSubdomain().high;

                        forall i in current_frontier {
                            if((xlocal(i, vertexBegin, vertexEnd))) { 
                                ref neighborhood = neighbor_complete[i];
                                forall j in neighborhood {
                                    if (depth[j] == -1) {
                                        depth[j] = cur_level + 1;
                                        next_frontier.add(j);
                                    }
                                }
                            } 
                        } //end forall
                    } // end on loc
                }// end coforall loc
                cur_level += 1;
                size_current_frontier = next_frontier.size;
                current_frontier <=> next_frontier;
                next_frontier.clear();
            }// end while 
            return "success";
        }// end of bfs_kernel_und_adj_list

        /* Merged the reversed arrays and regular arrays ala CSR style to maintain neighborhoods for each node
         * contiguously in an array. */
        proc bfs_kernel_und_complete_arrays(nei: [?D1] int, start_i: [?D2] int, src: [?D3] int, dst: [?D4] int, 
                                neiR: [?D5] int, start_iR: [?D6] int, srcR: [?D7] int, 
                                dstR: [?D8] int):string throws {            
            depth = -1;
            var cur_level = 0;
            var current_frontier = new DistBag(int, Locales);
            var next_frontier = new DistBag(int, Locales);
            current_frontier.add(root);
            var size_current_frontier = 1 : int;
            depth[root] = cur_level;

            while (size_current_frontier > 0) { 
                coforall loc in Locales {
                    on loc {
                        var edgeBegin = SRC_COMPLETE.localSubdomain().low;
                        var edgeEnd = SRC_COMPLETE.localSubdomain().high;
                        var vertexBegin = SRC_COMPLETE[edgeBegin];
                        var vertexEnd = SRC_COMPLETE[edgeEnd];

                        forall i in current_frontier {
                            if((xlocal(i, vertexBegin, vertexEnd))) { 
                                var numNF = NEI_COMPLETE[i];
                                var edgeId = START_I_COMPLETE[i];
                                var nextStart = max(edgeId, edgeBegin);
                                var nextEnd = min(edgeEnd, edgeId + numNF - 1);
                                ref neighborhood = DST_COMPLETE.localSlice(nextStart..nextEnd);
                                forall j in neighborhood {
                                    if (depth[j] == -1) {
                                        depth[j] = cur_level + 1;
                                        next_frontier.add(j);
                                    }
                                }
                            }
                        } //end forall
                    } // end on loc
                }// end coforall loc
                cur_level += 1;
                size_current_frontier = next_frontier.size;
                current_frontier <=> next_frontier;
                next_frontier.clear();
            }// end while 
            return "success";
        }// end of bfs_kernel_complete_arrays

        /**************************************/
        /* REMOTE DST AGGREGATOR METHOD BELOW */
        /**************************************/

        // Create global array to track the low subdomain of each locale so we know what locale
        // we must write the next frontier to. 
        var D_sbdmn = {0..numLocales-1} dmapped Replicated();
        var ranges : [D_sbdmn] (int,locale);

        // Write the local subdomain low value to the sizes array include the locale that owns that
        // particular range. 
        coforall loc in Locales {
            on loc {
                var lowVertex = SRC_COMPLETE[SRC_COMPLETE.localSubdomain().low];

                coforall rloc in Locales { 
                    on rloc {
                        ranges[loc.id] = (lowVertex,loc);
                    }
                }
            }
        }

        // Helper procedure to parse ranges and return the locale we must write to.
        proc find_locs(val:int) {
            var locs = new list(locale, parSafe=true);
            for i in 1..numLocales - 1 {
                if (val >= ranges[i-1][0] && val <= ranges[i][0]) {
                    locs.append(ranges[i-1][1]);
                }
                if (i == numLocales - 1) {
                    if val >= ranges[i][0] {
                        locs.append(ranges[i][1]);
                    }
                }
            }
            return locs.toArray();
        }

        /* Using the remote aggregator above for sets, we are going to perform aggregated writes to the
         * locales that include a sliver of the neighborhood to keep writing. Note: remote aggregator
         * written with a combo of the Arkouda dst aggregator and Thomas Rolinger's aggregator for 
         * dynamic arrays. */
        proc bfs_kernel_und_coarse_writes(nei: [?D1] int, start_i: [?D2] int, src: [?D3] int, dst: [?D4] int, 
                                neiR: [?D5] int, start_iR: [?D6] int, srcR: [?D7] int, 
                                dstR: [?D8] int):string throws {            
            depth = -1;
            var cur_level = 0;
            
            // The current and next frontiers for each locale. The frontiers hold the
            // vertex to process and its parent (i.e., the vertex who added it to the frontier
            // from the previous level). These are global (defined in Utils) so we can do
            // aggregation.
            var block_locale_D : domain(1) dmapped Block(boundingBox=LocaleSpace) = LocaleSpace;
            D_util = {0..1} dmapped Replicated();
            coforall loc in Locales do on loc {
                queues[0] = new set(int, parSafe=true);
                queues[1] = new set(int, parSafe=true);
            } 
            queueIdx = 0;
            
            // Add the root to the locale that owns it and update size & depth.
            for lc in find_locs(root) {
                on lc do queues[queueIdx].add(root);
            }
            var size_current_frontier:int = 1;
            depth[root] = cur_level;

            // coforall loc in Locales do on loc  {
            //     writeln("SRC_COMPLETE on loc ", loc, " = ", SRC_COMPLETE[SRC_COMPLETE.localSubdomain()]);
            // }
            // writeln();
            // coforall loc in Locales do on loc  {
            //     writeln("DST_COMPLETE on loc ", loc, " = ", DST_COMPLETE[DST_COMPLETE.localSubdomain()]);
            // }
            // writeln();

            while true { 
                var pending_work:bool;
                coforall loc in Locales with(|| reduce pending_work) {
                    on loc {
                        var edgeBegin = SRC_COMPLETE.localSubdomain().low;
                        var edgeEnd = SRC_COMPLETE.localSubdomain().high;
                        var vertexBegin = SRC_COMPLETE[edgeBegin];
                        var vertexEnd = SRC_COMPLETE[edgeEnd];
                        // writeln("queue on ", loc, " = ", queues[queueIdx]);
                        forall i in queues[queueIdx] with (|| reduce pending_work, var agg = new SetDstAggregator(int)) {
                            var numNF = NEI_COMPLETE[i];
                            var edgeId = START_I_COMPLETE[i];
                            var nextStart = max(edgeId, edgeBegin);
                            var nextEnd = min(edgeEnd, edgeId + numNF - 1);
                            ref neighborhood = DST_COMPLETE.localSlice(nextStart..nextEnd); // one way to improve performance is local slice
                            for j in neighborhood { /* can be forall? */
                                if (depth[j] == -1) {
                                    pending_work = true;
                                    depth[j] = cur_level + 1;
                                    var locs = find_locs(j);
                                    for lc in locs {
                                        agg.copy(lc.id, j); /* aggregator overall gives error: internal error: RES-LAT-ECK-0652 chpl version 1.30.0 */
                                    }
                                }
                            }
                        } //end forall
                        queues[queueIdx].clear();
                    } // end on loc
                }// end coforall loc
                // writeln("depth = ", depth);
                // writeln();
                if !pending_work {
                    break;
                }
                cur_level += 1;
                queueIdx = (queueIdx+1)%2;
            }// end while 
            return "success";
        }// end of bfs_kernel_coarse_writes

        rootN = msgArgs.getValueOf("Source");
        root = rootN:int;
        depth[root] = 0;

        proc return_depth(): string throws{
            var depthName = st.nextName();
            var depthEntry = new shared SymEntry(depth);
            st.addEntry(depthName, depthEntry);

            var depMsg =  'created ' + st.attrib(depthName);
            return depMsg;
        }

        if(!directed) {
            var timer:stopwatch;
            var size = 1;
            var times: [0..size-1] real;
            var it = 0;
            for t in times {
                timer.start();
                if it == size - 1 then startCommDiagnostics();
                bfs_kernel_und(
                    toSymEntry(ag.getComp("NEIGHBOR"), int).a,
                    toSymEntry(ag.getComp("START_IDX"), int).a,
                    toSymEntry(ag.getComp("SRC"), int).a,
                    toSymEntry(ag.getComp("DST"), int).a,
                    toSymEntry(ag.getComp("NEIGHBOR_R"), int).a,
                    toSymEntry(ag.getComp("START_IDX_R"), int).a,
                    toSymEntry(ag.getComp("SRC_R"), int).a,
                    toSymEntry(ag.getComp("DST_R"), int).a
                );
                timer.stop();
                if it == size - 1 then stopCommDiagnostics();
                t = timer.elapsed();
                timer.clear();
                it += 1;
            }
            var depth1 = depth;
            writeln("$$$$$$$$$$ Original BFS time elapsed = ", (+ reduce times) / times.size);
            printCommDiagnosticsTable();
            writeln();
            resetCommDiagnostics();

            it = 0;
            for t in times {
                timer.start();
                if it == size - 1 then startCommDiagnostics();
                bfs_kernel_und_concatenate(
                    toSymEntry(ag.getComp("NEIGHBOR"), int).a,
                    toSymEntry(ag.getComp("START_IDX"), int).a,
                    toSymEntry(ag.getComp("SRC"), int).a,
                    toSymEntry(ag.getComp("DST"), int).a,
                    toSymEntry(ag.getComp("NEIGHBOR_R"), int).a,
                    toSymEntry(ag.getComp("START_IDX_R"), int).a,
                    toSymEntry(ag.getComp("SRC_R"), int).a,
                    toSymEntry(ag.getComp("DST_R"), int).a
                );
                timer.stop();
                if it == size - 1 then stopCommDiagnostics();
                t = timer.elapsed();
                timer.clear();
                it += 1;
            }
            var depth2 = depth;
            writeln("$$$$$$$$$$ Neighbor concatenate BFS time elapsed = ", (+ reduce times) / times.size);
            printCommDiagnosticsTable();
            writeln();
            resetCommDiagnostics();

            it = 0;
            for t in times {
                timer.start();
                if it == size - 1 then startCommDiagnostics();
                bfs_kernel_und_cobegin(
                    toSymEntry(ag.getComp("NEIGHBOR"), int).a,
                    toSymEntry(ag.getComp("START_IDX"), int).a,
                    toSymEntry(ag.getComp("SRC"), int).a,
                    toSymEntry(ag.getComp("DST"), int).a,
                    toSymEntry(ag.getComp("NEIGHBOR_R"), int).a,
                    toSymEntry(ag.getComp("START_IDX_R"), int).a,
                    toSymEntry(ag.getComp("SRC_R"), int).a,
                    toSymEntry(ag.getComp("DST_R"), int).a
                );
                timer.stop();
                if it == size - 1 then stopCommDiagnostics();
                t = timer.elapsed();
                timer.clear();
                it += 1;
            }
            var depth3 = depth;
            writeln("$$$$$$$$$$ Neighbor cobegin BFS time elapsed = ", (+ reduce times) / times.size);
            printCommDiagnosticsTable();
            writeln();
            resetCommDiagnostics();

            it = 0;
            for t in times {
                timer.start();
                if it == size - 1 then startCommDiagnostics();
                bfs_kernel_und_adj_list(
                    toSymEntry(ag.getComp("NEIGHBOR"), int).a,
                    toSymEntry(ag.getComp("START_IDX"), int).a,
                    toSymEntry(ag.getComp("SRC"), int).a,
                    toSymEntry(ag.getComp("DST"), int).a,
                    toSymEntry(ag.getComp("NEIGHBOR_R"), int).a,
                    toSymEntry(ag.getComp("START_IDX_R"), int).a,
                    toSymEntry(ag.getComp("SRC_R"), int).a,
                    toSymEntry(ag.getComp("DST_R"), int).a
                );
                timer.stop();
                if it == size - 1 then stopCommDiagnostics();
                t = timer.elapsed();
                timer.clear();
                it += 1;
            }
            var depth4 = depth;
            writeln("$$$$$$$$$$ Neighbor complete BFS time elapsed = ", (+ reduce times) / times.size);
            printCommDiagnosticsTable();
            writeln();
            resetCommDiagnostics();

            it = 0;
            for t in times {
                timer.start();
                if it == size - 1 then startCommDiagnostics();
                bfs_kernel_und_complete_arrays(
                    toSymEntry(ag.getComp("NEIGHBOR"), int).a,
                    toSymEntry(ag.getComp("START_IDX"), int).a,
                    toSymEntry(ag.getComp("SRC"), int).a,
                    toSymEntry(ag.getComp("DST"), int).a,
                    toSymEntry(ag.getComp("NEIGHBOR_R"), int).a,
                    toSymEntry(ag.getComp("START_IDX_R"), int).a,
                    toSymEntry(ag.getComp("SRC_R"), int).a,
                    toSymEntry(ag.getComp("DST_R"), int).a
                );
                timer.stop();
                if it == size - 1 then stopCommDiagnostics();
                t = timer.elapsed();
                timer.clear();
                it += 1;
            }
            var depth5 = depth;
            writeln("$$$$$$$$$$ Complete array BFS time elapsed = ", (+ reduce times) / times.size);
            printCommDiagnosticsTable();
            writeln();
            resetCommDiagnostics();

            it = 0;
            for t in times {
                timer.start();
                if it == size - 1 then startCommDiagnostics();
                bfs_kernel_und_coarse_writes(
                    toSymEntry(ag.getComp("NEIGHBOR"), int).a,
                    toSymEntry(ag.getComp("START_IDX"), int).a,
                    toSymEntry(ag.getComp("SRC"), int).a,
                    toSymEntry(ag.getComp("DST"), int).a,
                    toSymEntry(ag.getComp("NEIGHBOR_R"), int).a,
                    toSymEntry(ag.getComp("START_IDX_R"), int).a,
                    toSymEntry(ag.getComp("SRC_R"), int).a,
                    toSymEntry(ag.getComp("DST_R"), int).a
                );
                timer.stop();
                if it == size - 1 then stopCommDiagnostics();
                t = timer.elapsed();
                timer.clear();
                it += 1;
            }
            var depth6 = depth;
            writeln("$$$$$$$$$$ Aggregated BFS time elapsed = ", (+ reduce times) / times.size);
            printCommDiagnosticsTable();
            writeln();
            resetCommDiagnostics();

            var error = false;
            for (i,j,k,l,m,n) in zip(depth1, depth2, depth3, depth4, depth5, depth6) {
                if error {
                    writeln("ERROR! DEPTHS DO NOT MATCH UP.");
                    break;
                }

                if(i != j) then error = true;
                if(i != k) then error = true;
                if(i != l) then error = true;
                if(i != m) then error = true;
                if(i != n) then error = true;
            }
            repMsg=return_depth();
        }
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
        return new MsgTuple(repMsg, MsgType.NORMAL);
    }

    use CommandMap;
    registerFunction("segmentedGraphBFS", segBFSMsg, getModuleName());
}