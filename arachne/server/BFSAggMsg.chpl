module BFSAggMsg {
    // Chapel modules.
    use Reflection;
    use Set;
    use List;
    use Time;
    use CommDiagnostics;
    use ReplicatedDist;

    // Package modules. 
    use DistributedBag;
    
    // Arachne modules.
    use GraphArray;
    use Utils;
    use BuildGraphMsg;
    use Aggregators;
    
    // Arkouda modules.
    use MultiTypeSymbolTable;
    use MultiTypeSymEntry;
    use ServerConfig;
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
    * msgArgs: arguments passed to backend. 
    * SymTab: symbol table used for storage. 
    *
    * returns: message back to Python.
    */
    proc segBFSMsgAgg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        var repMsg: string;
        var depthName:string;

        var n_verticesN = msgArgs.getValueOf("NumOfVertices");
        var n_edgesN = msgArgs.getValueOf("NumOfEdges");
        var directedN = msgArgs.getValueOf("Directed");
        var weightedN = msgArgs.getValueOf("Weighted");
        var graphEntryName = msgArgs.getValueOf("GraphName");
        var rootN = msgArgs.getValueOf("Source");

        var Nv = n_verticesN:int;
        var Ne = n_edgesN:int;
        var directed = directedN:int:bool;
        var weighted = weightedN:int:bool;

        var root = rootN:int; 
        var srcN, dstN, startN, neighborN, eweightN: string; 
        var srcRN, dstRN, startRN, neighborRN: string; 
        var gEntry: borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st); 
        var ag = gEntry.graph;

        // Create empty depth array to return at the end of execution. 
        var depth = makeDistArray(Nv, int);
        depth = -1;

        /**********************************************/
        /* MERGE REVERSED ARRAYS INTO REGULAR ARRAYS. */
        /* THIS CODE WILL NOT REMAIN BUT WILL BE MOVED*/
        /* WHERE WE BUILD OUR GRAPHS!                 */
        /**********************************************/
        var NEI = toSymEntry(ag.getComp("NEIGHBOR"), int).a;
        var START_I = toSymEntry(ag.getComp("START_IDX"), int).a;
        var SRC = toSymEntry(ag.getComp("SRC"), int).a;
        var DST = toSymEntry(ag.getComp("DST"), int).a;
        var NEIR = toSymEntry(ag.getComp("NEIGHBOR_R"), int).a;
        var START_IR = toSymEntry(ag.getComp("START_IDX_R"), int).a;
        var SRCR = toSymEntry(ag.getComp("SRC_R"), int).a;
        var DSTR = toSymEntry(ag.getComp("DST_R"), int).a;
        var SRC_COMPLETE = makeDistArray(SRC.size + DST.size, int);
        var DST_COMPLETE: [SRC_COMPLETE.domain] int;
        
        SRC_COMPLETE[SRC.domain] = SRC;
        DST_COMPLETE[SRC.domain] = DST;

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

        /** 
        * Using the remote aggregator above for sets, we are going to perform aggregated writes to the
        * locales that include a sliver of the neighborhood. 
        *
        * graph: graph to run bfs on. 
        *
        * returns: success string message. */
        proc bfs_kernel_und_agg(graph: SegGraph):string throws {
            
            var D_frontier_sets = {0..1} dmapped Replicated();
            var frontier_sets : [D_frontier_sets] set(int, parSafe=true);
            var frontier_sets_idx : int;
            coforall loc in Locales do on loc {
                frontier_sets[0] = new set(int, parSafe=true);
                frontier_sets[1] = new set(int, parSafe=true);
            } 
            frontier_sets_idx = 0;
            
            // Add the root to the locale that owns it and update size & depth.
            for lc in find_locs(root) {
                on lc do frontier_sets[frontier_sets_idx].add(root);
            }
            depth = -1;
            var cur_level = 0;
            depth[root] = cur_level;

            while true { 
                var pending_work:bool;
                coforall loc in Locales with(|| reduce pending_work) {
                    on loc {
                        var edgeBegin = SRC_COMPLETE.localSubdomain().low;
                        var edgeEnd = SRC_COMPLETE.localSubdomain().high;
                        var vertexBegin = SRC_COMPLETE[edgeBegin];
                        var vertexEnd = SRC_COMPLETE[edgeEnd];
                        forall i in frontier_sets[frontier_sets_idx] with (|| reduce pending_work, var agg = new SetDstAggregator(int)) {
                            var numNF = NEI_COMPLETE[i];
                            var edgeId = START_I_COMPLETE[i];
                            var nextStart = max(edgeId, edgeBegin);
                            var nextEnd = min(edgeEnd, edgeId + numNF - 1);
                            ref neighborhood = DST_COMPLETE.localSlice(nextStart..nextEnd);
                            // TODO: forall possibly? Gives error since agg has to be passed.
                            for j in neighborhood { 
                                if (depth[j] == -1) {
                                    pending_work = true;
                                    depth[j] = cur_level + 1;
                                    var locs = find_locs(j);
                                    for lc in locs {
                                        agg.copy(lc.id, j);
                                    }
                                }
                            }
                        } //end forall
                        frontier_sets[frontier_sets_idx].clear();
                    } // end on loc
                }// end coforall loc
                if !pending_work {
                    break;
                }
                cur_level += 1;
                frontier_sets_idx = (frontier_sets_idx + 1) % 2;
            }// end while 
            return "success";
        }// end of bfs_kernel_agg

        proc return_depth(): string throws{
            var depthName = st.nextName();
            var depthEntry = new shared SymEntry(depth);
            st.addEntry(depthName, depthEntry);

            var depMsg =  'created ' + st.attrib(depthName);
            return depMsg;
        }

        var timer:stopwatch;
        var size = 10;
        var times: [0..size-1] real;
        var it = 0;

        for t in times {
            timer.start();
            if it == size - 1 then startCommDiagnostics();
            bfs_kernel_und_agg(ag);
            timer.stop();
            if it == size - 1 then stopCommDiagnostics();
            t = timer.elapsed();
            timer.clear();
            it += 1;
        }
        writeln("$$$$$$$$$$ Aggregated BFS time elapsed = ", (+ reduce times) / times.size);
        printCommDiagnosticsTable();
        writeln();
        resetCommDiagnostics();

        repMsg=return_depth();
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
        return new MsgTuple(repMsg, MsgType.NORMAL);
    }

    use CommandMap;
    registerFunction("segmentedGraphBFSagg", segBFSMsgAgg, getModuleName());
}