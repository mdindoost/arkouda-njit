module BFSMsg {
    // Chapel modules.
    use IO;
    use Reflection;
    use Set;
    use Time; 
    use Sort;
    use List;
    use CommDiagnostics;

    // Package modules. 
    use DistributedBag; 
    
    // Arachne modules.
    use GraphArray;
    use Utils;
    use BuildGraphMsg;
    
    // Arkouda modules.
    use MultiTypeSymbolTable;
    use MultiTypeSymEntry;
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

        timer.start();

        // Create empty depth array to return at the end of execution. 
        var depth = makeDistArray(Nv, int);
        depth = -1;

        /**
        * BFS kernel for undirected graphs. 
        *
        * nei: neighbor array
        * start_i: starting edge array location given vertex v
        * src: source array
        * dst: destination array
        * neiR: reversed neighbor array
        * start_iR: reversed starting edge array location given vertex v
        * srcR: reversed source array
        * dstR: reversed destination array
        *
        * returns: message back to Python.
        */
        proc bfs_kernel_und_original(nei: [?D1] int, start_i: [?D2] int, src: [?D3] int, dst: [?D4] int, 
                                neiR: [?D5] int, start_iR: [?D6] int, srcR: [?D7] int, 
                                dstR: [?D8] int):string throws {            
            depth = -1;
            var cur_level = 0;
            var SetCurF = new DistBag(int, Locales); // use bag to keep the current frontier
            var SetNextF = new DistBag(int, Locales); // use bag to keep the next frontier
            SetCurF.add(root);
            var numCurF = 1 : int;
            depth[root] = 0;
            while (numCurF > 0) {
                coforall loc in Locales  with (ref SetNextF) {
                    on loc {
                        ref srcf = src;
                        ref df = dst;
                        ref nf = nei;
                        ref sf = start_i;

                        ref srcfR = srcR;
                        ref dfR = dstR;
                        ref nfR = neiR;
                        ref sfR = start_iR;

                        var edgeBegin = src.localSubdomain().low;
                        var edgeEnd = src.localSubdomain().high;
                        var vertexBegin = src[edgeBegin];
                        var vertexEnd = src[edgeEnd];
                        var vertexBeginR = srcR[edgeBegin];
                        var vertexEndR = srcR[edgeEnd];

                        forall i in SetCurF with (ref SetNextF) {
                            // current edge has the vertex
                            if((xlocal(i, vertexBegin, vertexEnd))) { 
                                var numNF = nf[i];
                                var edgeId = sf[i];
                                var nextStart = max(edgeId, edgeBegin);
                                var nextEnd = min(edgeEnd, edgeId + numNF - 1);
                                ref NF = df[nextStart..nextEnd];
                                forall j in NF with (ref SetNextF){
                                    if (depth[j] == -1) {
                                        depth[j] = cur_level + 1;
                                        SetNextF.add(j);
                                    }
                                }
                            } 
                            if ((xlocal(i, vertexBeginR, vertexEndR))) {
                                var numNF = nfR[i];
                                var edgeId = sfR[i];
                                var nextStart = max(edgeId, edgeBegin);
                                var nextEnd = min(edgeEnd, edgeId + numNF - 1);
                                ref NF = dfR[nextStart..nextEnd];
                                forall j in NF with (ref SetNextF)  {
                                    if (depth[j] == -1) {
                                        depth[j] = cur_level+1;
                                        SetNextF.add(j);
                                    }
                                }
                            }
                        } //end forall
                    } // end on loc
                }// end coforall loc
                cur_level += 1;
                numCurF = SetNextF.getSize();
                SetCurF <=> SetNextF;
                SetNextF.clear();
            }// end while 
            return "success";
        }// end of fo_bag_bfs_kernel_u
        
        /**
        * BFS kernel for undirected graphs. 
        *
        * nei: neighbor array
        * start_i: starting edge array location given vertex v
        * src: source array
        * dst: destination array
        * neiR: reversed neighbor array
        * start_iR: reversed starting edge array location given vertex v
        * srcR: reversed source array
        * dstR: reversed destination array
        *
        * returns: message back to Python.
        */
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
                // var locs = new set(int, parSafe=true);
                // var locs_size: [0..numLocales-1] atomic int;
                // var num_local_reg: [0..numLocales-1] atomic int;
                // var num_local_rev: [0..numLocales-1] atomic int;
                // locs_size = 0;
                // num_local_reg = 0;
                // num_local_rev = 0;
                // forall u in current_frontier with (ref locs){
                //     locs.add(here.id);
                //     locs_size[here.id].add(1);
                // }

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
                        } //end forall
                    } // end on loc
                }// end coforall loc
                // writeln("locs = ", locs, " with size = ", locs_size, " processed vertices reg = ", num_local_reg, " processed vertices rev = ", num_local_rev);

                cur_level += 1;
                size_current_frontier = next_frontier.size;
                current_frontier <=> next_frontier;
                next_frontier.clear();
            }// end while 
            return "success";
        }// end of bfs_kernel_und()

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

            ref neighborhood = DST[start..end-1];

            forall v in neighborhood {
                neighbor_complete[u].append(v);
            }
        }

        forall u in NEIR.domain {
            var start = START_IR[u];
            var end = start + NEIR[u];

            ref neighborhoodR = DSTR[start..end-1];

            forall v in neighborhoodR {
                neighbor_complete[u].append(v);
            }
        }

        /* MERGE REVERSED ARRAYS INTO REGULAR ARRAYS */
        var SRC_COMPLETE = makeDistArray(SRC.size + DST.size, int);
        var DST_COMPLETE: [SRC_COMPLETE.domain] int;
        
        forall i in SRC.domain { 
            SRC_COMPLETE[i] = SRC[i];
            DST_COMPLETE[i] = DST[i];
        }
        var final_i_start = SRC.size;
        var final_i_end = final_i_start + SRC.size;
        for (i,j) in zip(final_i_start..final_i_end, SRC.domain) {
            SRC_COMPLETE[i] = DST[j];
            DST_COMPLETE[i] = SRC[j];
        }
        var e_weight: [SRC_COMPLETE.domain] real;
        combine_sort(SRC_COMPLETE, DST_COMPLETE, e_weight, false, false);

        var nv = new set(int, parSafe=true);
        forall u in SRC_COMPLETE with (ref nv) {
            nv.add(u);
        }
        var NEI_COMPLETE = makeDistArray(nv.size, int);
        var START_I_COMPLETE: [NEI_COMPLETE.domain] int;

        // writeln("SRC = ", SRC);
        // writeln("DST = ", DST);
        
        // for (u,v) in zip(SRC_COMPLETE, DST_COMPLETE) {
        //     writeln(u, " ", v);
        // }
        
        writeln("SRC SIZE = ", SRC.size);
        writeln("SRCR SIZE = ", SRCR.size);
        writeln("SRC_COMPLETE SIZE = ", SRC_COMPLETE.size);
        writeln("NEI SIZE = ", NEI.size);
        writeln("START_I_COMPLETE SIZE = ", START_I_COMPLETE.size);
        writeln("NEI_COMPLETE SIZE = ", NEI_COMPLETE.size);

        set_neighbor(SRC_COMPLETE, START_I_COMPLETE, NEI_COMPLETE);

        proc bfs_kernel_und_neighbor_complete(nei: [?D1] int, start_i: [?D2] int, src: [?D3] int, dst: [?D4] int, 
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
                // var locs = new set(int, parSafe=true);
                // var locs_size: [0..numLocales-1] atomic int;
                // var num_local_reg: [0..numLocales-1] atomic int;
                // var num_local_rev: [0..numLocales-1] atomic int;
                // locs_size = 0;
                // num_local_reg = 0;
                // num_local_rev = 0;
                // forall u in current_frontier with (ref locs){
                //     locs.add(here.id);
                //     locs_size[here.id].add(1);
                // }

                coforall loc in Locales {
                    on loc {
                        var vertexBegin = nei.localSubdomain().low;
                        var vertexEnd = nei.localSubdomain().high;

                        forall i in current_frontier {
                            if((xlocal(i, vertexBegin, vertexEnd))) { 
                                // var numNF = nei[i];
                                // var edgeId = start_i[i];
                                // var nextStart = max(edgeId, edgeBegin);
                                // var nextEnd = min(edgeEnd, edgeId + numNF - 1);
                                // num_local_reg[here.id].add(1);
                                ref neighborhood = neighbor_complete[i];
                                forall j in neighborhood {
                                    if (depth[j] == -1) {
                                        depth[j] = cur_level + 1;
                                        next_frontier.add(j);
                                    }
                                }
                            } 
                            // if ((xlocal(i, vertexBeginR, vertexEndR))) {
                            //     var numNF = neiR[i];
                            //     var edgeId = start_iR[i];
                            //     var nextStart = max(edgeId, edgeBegin);
                            //     var nextEnd = min(edgeEnd, edgeId + numNF - 1);
                            //     // num_local_rev[here.id].add(1);
                            //     ref neighborhoodR = dstR[nextStart..nextEnd];
                            //     forall j in neighborhoodR {
                            //         if (depth[j] == -1) {
                            //             depth[j] = cur_level + 1;
                            //             next_frontier.add(j);
                            //         }
                            //     }
                            // }
                        } //end forall
                    } // end on loc
                }// end coforall loc
                // writeln("locs = ", locs, " with size = ", locs_size, " processed vertices reg = ", num_local_reg, " processed vertices rev = ", num_local_rev);

                cur_level += 1;
                size_current_frontier = next_frontier.size;
                current_frontier <=> next_frontier;
                next_frontier.clear();
            }// end while 
            return "success";
        }// end of bfs_kernel_und_neighbor_complete()

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
                // var locs = new set(int, parSafe=true);
                // var locs_size: [0..numLocales-1] atomic int;
                // var num_local_reg: [0..numLocales-1] atomic int;
                // var num_local_rev: [0..numLocales-1] atomic int;
                // locs_size = 0;
                // num_local_reg = 0;
                // num_local_rev = 0;
                // forall u in current_frontier with (ref locs){
                //     locs.add(here.id);
                //     locs_size[here.id].add(1);
                // }

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
                                // num_local_reg[here.id].add(1);
                                ref neighborhood = DST_COMPLETE[nextStart..nextEnd];
                                forall j in neighborhood {
                                    if (depth[j] == -1) {
                                        depth[j] = cur_level + 1;
                                        next_frontier.add(j);
                                    }
                                }
                            } 
                            // if ((xlocal(i, vertexBeginR, vertexEndR))) {
                            //     var numNF = neiR[i];
                            //     var edgeId = start_iR[i];
                            //     var nextStart = max(edgeId, edgeBegin);
                            //     var nextEnd = min(edgeEnd, edgeId + numNF - 1);
                            //     // num_local_rev[here.id].add(1);
                            //     ref neighborhoodR = dstR[nextStart..nextEnd];
                            //     forall j in neighborhoodR {
                            //         if (depth[j] == -1) {
                            //             depth[j] = cur_level + 1;
                            //             next_frontier.add(j);
                            //         }
                            //     }
                            // }
                        } //end forall
                    } // end on loc
                }// end coforall loc
                // writeln("locs = ", locs, " with size = ", locs_size, " processed vertices reg = ", num_local_reg, " processed vertices rev = ", num_local_rev);

                cur_level += 1;
                size_current_frontier = next_frontier.size;
                current_frontier <=> next_frontier;
                next_frontier.clear();
            }// end while 
            return "success";
        }// end of bfs_kernel_complete_arrays()

        /**
        * BFS kernel for directed graphs. 
        *
        * nei: neighbor array
        * start_i: starting edge array location given vertex v
        * src: source array
        * dst: destination array
        *
        * returns: message back to Python.
        */
        proc bfs_kernel_dir( nei: [?D1] int, start_i: [?D2] int, src: [?D3] int, 
                                  dst: [?D4] int): string throws {
            depth = -1;
            var cur_level = 0;
            var current_frontier = new DistBag(int, Locales);
            var next_frontier = new DistBag(int, Locales);
            current_frontier.add(root);
            var size_current_frontier = 1 : int;
            depth[root] = cur_level;

            while (size_current_frontier > 0) {
               coforall loc in Locales  with (ref next_frontier) {
                    on loc {
                        var edgeBegin = src.localSubdomain().low;
                        var edgeEnd = src.localSubdomain().high;
                        var vertexBegin = src[edgeBegin];
                        var vertexEnd = src[edgeEnd];

                        forall i in current_frontier with (ref next_frontier) {
                            if((xlocal(i, vertexBegin, vertexEnd))) { 
                                var numNF = nei[i];
                                var edgeId = start_i[i];
                                var nextStart = max(edgeId, edgeBegin);
                                var nextEnd = min(edgeEnd, edgeId + numNF - 1);
                                ref neighborhood = dst[nextStart..nextEnd];
                                forall j in neighborhood with (ref next_frontier){
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
        }//end of fo_bag_bfs_kernel_d

        rootN = msgArgs.getValueOf("Source");
        root = rootN:int;
        depth[root]=0;

        proc return_depth(): string throws{
            var depthName = st.nextName();
            var depthEntry = new shared SymEntry(depth);
            st.addEntry(depthName, depthEntry);

            var depMsg =  'created ' + st.attrib(depthName);
            return depMsg;
        }

        if(directed) {
            bfs_kernel_dir(
                toSymEntry(ag.getComp("NEIGHBOR"), int).a,
                toSymEntry(ag.getComp("START_IDX"), int).a,
                toSymEntry(ag.getComp("SRC"), int).a,
                toSymEntry(ag.getComp("DST"), int).a
            );
            repMsg=return_depth();
        } else {
            var timer:stopwatch;
            var size = 5;
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
                bfs_kernel_und_neighbor_complete(
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
            var depth3 = depth;
            writeln("$$$$$$$$$$ Complete array BFS time elapsed = ", (+ reduce times) / times.size);
            printCommDiagnosticsTable();
            writeln();
            resetCommDiagnostics();

            var error = false;
            for (i,j,k) in zip(depth1, depth2, depth3) {
                if error {
                    writeln("ERROR! DEPTHS DO NOT MATCH UP.");
                    break;
                }

                if(i != j) then error = true;
                if(i != k) then error = true;
                if(j != k) then error = true;
            }
            repMsg=return_depth();
        }
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
        return new MsgTuple(repMsg, MsgType.NORMAL);
    }

    use CommandMap;
    registerFunction("segmentedGraphBFS", segBFSMsg, getModuleName());
}