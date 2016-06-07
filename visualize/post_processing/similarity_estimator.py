import argparse
import os
import collections
import numpy as np
import json

from matplotlib import pyplot as plt
from scipy.cluster.hierarchy import dendrogram, linkage, single
from scipy.spatial.distance import squareform

THRESHOLD = 0.85

if __name__ == "__main__":
    """ Main Start """

    parser = argparse.ArgumentParser()
    parser.add_argument('normalized_files_directory', type=str, help="The directory that contains all normalized files.")
    args = parser.parse_args()

    data = collections.defaultdict(list)
    max_block = -1

    # Read each individual back trace file and for each block, store a tuple with its taintID,
    # along with its corresponding normalized form.
    for dir_entry in os.listdir(args.normalized_files_directory):
        dir_entry_path = os.path.join(args.normalized_files_directory, dir_entry)
        if os.path.isfile(dir_entry_path):
            # Extract the block number and its taint.
            dir_entry_tokens = dir_entry.split('.')
            block = int(dir_entry_tokens[0])
            taintID = int(dir_entry_tokens[1])

            # Find the maximum block number.
            if block > max_block:
                max_block = block

            with open(dir_entry_path, 'r') as back_trace_file:
                # Read the normalized form into a list.
                normalized_data = back_trace_file.readlines()
                data[block].append((taintID, normalized_data))
                # print("File: {}.{}\n{}\n").format(block, taintID, normalized_data)

    similar_blocks = dict()
    for block_number, block_entries in data.items():
        for other_block_number, other_block_entries in data.items():
            # Compare only different blocks.
            if block_number != other_block_number:
                # Check all different combinations, based on the taintIDs stored for each block.
                for first_entry in block_entries:
                    for second_entry in other_block_entries:
                        first_taintID = first_entry[0]
                        first_normalized_set = set(first_entry[1])

                        second_taintID = second_entry[0]
                        second_normalized_set = set(second_entry[1])

                        intersection_length = len(first_normalized_set.intersection(second_normalized_set))
                        union_length = len(first_normalized_set.union(second_normalized_set))

                        # print("Block {0}.{1}\tBlock {2}.{3}\tJaccard: {4:.2f}\t|Intersection|: {5}\t|Union|: {6}").\
                        #     format(first_block, first_taintID, second_block, second_taintID,
                        #            intersection_length / float(union_length),
                        #            intersection_length, union_length)

                        jaccard_similarity = intersection_length / float(union_length)
                        if jaccard_similarity >= THRESHOLD:
                            # Mark the two blocks as similar, but only once; avoid symmetric tuples. In case the
                            # specified tuple exists, store the maximum Jaccard similarity.
                            if (block_number, other_block_number) in similar_blocks:
                                stored_jaccard_similarity = similar_blocks[(block_number, other_block_number)]
                                if stored_jaccard_similarity < jaccard_similarity:
                                    similar_blocks[(block_number, other_block_number)] = jaccard_similarity
                            elif (other_block_number, block_number) in similar_blocks:
                                stored_jaccard_similarity = similar_blocks[(other_block_number, block_number)]
                                if stored_jaccard_similarity < jaccard_similarity:
                                    similar_blocks[(other_block_number, block_number)] = jaccard_similarity
                            else:
                                similar_blocks[(block_number, other_block_number)] = jaccard_similarity

    # Create a list that contains the "distance" between all blocks. The list adheres to the condensed distance
    # matrix form returned by the pdist function:
    # http://docs.scipy.org/doc/scipy-0.14.0/reference/generated/scipy.spatial.distance.pdist.html
    #
    # The distance is calculated using the following formula:
    # dist(b1, b2) = 1 - jaccard_similarity(b1, b2).
    #
    # If the jaccard similarity is not calculated for two blocks, then their distance is defined to be infinite.
    #
    pdist_list = []
    for i in xrange(0, max_block + 1):
        for j in xrange(i + 1, max_block + 1):
            if (i, j) in similar_blocks:
                pdist_list.append(1.0 - similar_blocks[(i, j)])
            elif (j, i) in similar_blocks:
                pdist_list.append(1.0 - similar_blocks[(j, i)])
            else:
                pdist_list.append(np.inf)

    # Convert the list of distances into an numpy array and invoke the clustering algorithm.
    pdist_array = np.asarray(pdist_list)
    clustering_result = linkage(pdist_array, method='single')

    # Process the result in order to find the actual formed clusters of blocks.
    clusters = collections.defaultdict(list)
    clusterID = max_block + 1
    for i in xrange(0, len(clustering_result)):
        # Exit after encountering the first infinite distance.
        if not np.isfinite(clustering_result[i][2]):
            break

        if clustering_result[i][0] in clusters:
            clusters[clusterID + i] += clusters[clustering_result[i][0]]
            del clusters[clustering_result[i][0]]
        else:
            clusters[clusterID + i] += [clustering_result[i][0]]

        if clustering_result[i][1] in clusters:
            clusters[clusterID + i] += clusters[clustering_result[i][1]]
            del clusters[clustering_result[i][1]]
        else:
            clusters[clusterID + i] += [clustering_result[i][1]]

    # print(clusters)

    # Write the results into a .txt file for improved readability.
    with open('/tmp/clustering_results.txt', 'w') as f:
        json.dump(clusters, f)
        f.write('\n')