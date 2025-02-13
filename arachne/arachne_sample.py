"""Sample Arachne Script

This script provides an example on how a graph is built in Arachne from two Arkouda arrays and then
analyzed using Arachne functions. The graphs are randomly generated by using the ak.randint function
with the range of the vertex names being picked from 0..<n and the number of edges m. No special
distribution is used to generated the graph e.g. RMAT. Further, these graphs are population with 
labels and relationships picked from x random labels and y random relationships.

The values of n and m are accepted from command line input and they denote the size of the graph. 
The values of x and y are accepted from the command line input and they denote the number of labels 
and relationships, respectively that the graph will contain. It requires Arkouda and Arachne to both
be pip installed in the environment. 

Assumes Arkouda server is running. It will shutdown the Arkouda server upon completion.

Sample usage: python3 arachne_simple_tests.py n25 5555 1000 1000000 10 10

"""
import argparse
import time
import arkouda as ak
import arachne as ar

def create_parser():
    """Creates the command line parser for this script"""
    parser = argparse.ArgumentParser(
        description="Simple script showcasing all the functionality of Arachne on a random graph of\
                     size specified by the user."
    )
    parser.add_argument("hostname", help="Hostname of arkouda server")
    parser.add_argument("port", type=int, default=5555, help="Port of arkouda server")
    parser.add_argument("n", type=int, default=1000, help="Number of vertices for graph")
    parser.add_argument("m", type=int, default=1000000, help="Number of edges for graph")
    parser.add_argument("x", type=int, default=10, help="Number of labels for graph")
    parser.add_argument("y", type=int, default=10, help="Number of relationships for graph")

    return parser

if __name__ == "__main__":
    # Command line parser and extraction.
    sample_parser = create_parser()
    args = sample_parser.parse_args()

    # Connect to the Arkouda server.
    ak.verbose = False
    ak.connect(args.hostname, args.port)

    # Get Arkouda server configuration information.
    config = ak.get_config()
    num_locales = config["numLocales"]
    num_pus = config["numPUs"]
    print(f"Arkouda server running with {num_locales} locales and {num_pus} cores.")

    ### Build graph from randomly generated source and destination arrays.
    # 1. Use Arkouda's randint to generate the random edge arrays.
    src = ak.randint(0, args.n, args.m)
    dst = ak.randint(0, args.n, args.m)

    # 2. Build property graph from randomly generated edges.
    print()
    print("### BUILD AND POPULATE A PROPERTY GRAPH WITH RANDOM EDGES:")
    prop_graph = ar.PropGraph()
    start = time.time()
    prop_graph.add_edges_from(src, dst)
    end = time.time()
    build_time = end - start
    print(f"Building property graph with {len(prop_graph)} vertices and {prop_graph.size()} "
          f"edges took {round(build_time,2)} seconds.")

    ### Populate property graph with vertex labels.
    # 1. Generate labels.
    LBL = "label"
    labels_list = [LBL + str(x) for x in range(args.x)]
    labels = ak.array(labels_list)

    # 2. Generate random array of vertices with original vertex values.
    vertices = prop_graph.nodes()
    vertices_with_labels = ak.randint(0, len(prop_graph), len(prop_graph), seed=512)
    vertices_with_labels = vertices[vertices_with_labels]

    # 3. Generate random array of labels of the same size as the random array of vertices above.
    random_labels = ak.randint(0, len(labels), len(vertices_with_labels), seed=256)
    random_labels = labels[random_labels]

    # 4. Pack the values into a dataframe and populate them into the graph.
    label_df = ak.DataFrame({"vertex_ids" : vertices_with_labels, "vertex_labels" : random_labels})

    start = time.time()
    prop_graph.add_node_labels(label_df)
    end = time.time()
    add_labels_time = end - start
    print(f"Populating property graph with {len(random_labels)} labels took "
          f"{round(add_labels_time,2)} seconds.")

    ### Populate property graph with edge relationships.
    # 1. Generate labels.
    REL = "relationship"
    relationships_list = [REL + str(y) for y in range(args.y)]
    relationships = ak.array(relationships_list)

    # 2. Generate random array of edges with original vertex values.
    edges_with_relationships = ak.randint(0, prop_graph.size(), prop_graph.size(), seed=128)
    src_vertices_with_relationships = src[edges_with_relationships]
    dst_vertices_with_relationships = dst[edges_with_relationships]

    # 3. Generate random array of relationships of the same size as the random array of edges above.
    random_relationships = ak.randint(0, len(relationships), len(edges_with_relationships), seed=64)
    random_relationships = relationships[random_relationships]

    # 4. Pack the values into a dataframe and populate them into the graph.
    relationships_df = ak.DataFrame({"src" : src_vertices_with_relationships,
                                     "dst" : dst_vertices_with_relationships,
                                     "edge_relationships" : random_relationships})

    start = time.time()
    prop_graph.add_edge_relationships(relationships_df)
    end = time.time()
    add_relationships_time = end - start
    print(f"Populating property graph with {len(random_relationships)} relationships took "
          f"{round(add_relationships_time,2)} seconds.")

    ### Property graph operations. Currently, there are two types of queries avaialble: "or" and
    ### "and". If "or" is selected then the edges and/or vertices that contain at least one of the
    ### strings from the search space is returned. If "and" is selected then the edges and/or
    ### vertices thatc ontain ALL of the strings from the search space is returned. The function
    ### for one_path returns the intersection of the edges returned with the vertices returned.
    ### The same operations "or" and "and" can be selected for labels and relationships in one_path.
    print()
    print("### QUERY PROPERTY GRAPH LABELS AND RELATIONSHIPS.")
    # 1. Query labels with operation "or".
    labels_to_find = ak.array(labels_list[1:4])
    start = time.time()
    queried_nodes_or = prop_graph.query_labels(labels_to_find, op = "or")
    end = time.time()
    or_query_labels_time = end - start
    print(f"Querying {len(labels_to_find)} node labels with OR took "
          f"{round(or_query_labels_time, 2)} seconds and returned array of size "
          f"{len(queried_nodes_or)}.")

    # 2. Query relationships with operation "or".
    relationships_to_find = ak.array(relationships_list[1:4])
    start = time.time()
    queried_edges_or = prop_graph.query_relationships(relationships_to_find, op = "or")
    end = time.time()
    or_query_relationships_time = end - start
    print(f"Querying {len(relationships_to_find)} edge relationships with OR took "
          f"{round(or_query_relationships_time, 2)} seconds and returned array of size "
          f"{len(queried_edges_or[1])}.")

    # 3. Run one_path function that returns paths of length one (edges) that match the queries. Uses
    #    operation "or" for both labels and relationships.
    start = time.time()
    queried_edges = prop_graph.one_path(labels_to_find, relationships_to_find, "or", "or")
    end = time.time()
    one_path_time = end - start
    print(f"Running one_path with OR operations on both labels and relationships took "
          f"{round(one_path_time, 2)} seconds and returned array of size {len(queried_edges[1])}.")

    ### Build new graph with returned edges from one_path and run breadth_first_search on it.
    print()
    print("### BUILD NEW DIGRAPH FROM ONE_PATH EDGE RESULTS AND RUN BREADTH-FIRST SEARCH ON IT.")
    # 1. Build the graph first.
    graph = ar.DiGraph()
    start = time.time()
    graph.add_edges_from(queried_edges[0], queried_edges[1])
    end = time.time()
    build_time = end - start
    print(f"Building graph with {len(graph)} vertices and {graph.size()} edges took "
          f"{round(build_time,2)} seconds.")

    # 2. Run breadth-first search on the graph from highest out degree node.
    highest_out_degree = ak.argmax(graph.out_degree())
    start = time.time()
    depths = ar.bfs_layers(graph, int(graph.nodes()[highest_out_degree]))
    end = time.time()
    bfs_time = round(end-start,2)
    print(f"Running breadth-first search on directed graph took {bfs_time} seconds.")

    # 3. Use depth to return one of the vertices with highest depth.
    print(f"One of the vertices with highest depth was: {graph.nodes()[ak.argmax(depths)]}.")

    ak.shutdown()
