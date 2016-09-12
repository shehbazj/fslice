import sys
import os
from random import randint

MAX_FILE_OR_DIR = 40
BLOCK_SIZE = 64

percent = 20
depth = 0
dir_percentage = 20
min_filesize = 20
max_filesize = 100 
num_files = 0



def generateFileArray(min_filesize, max_filesize, num_files):

    fileArray = []
    availableBytes = (BLOCK_SIZE * 512 * percent ) / 100
    print "Available Bytes " , availableBytes
    fileBytes = (availableBytes * (100 - dir_percentage)) / 100

    REMAINING_BYTES = fileBytes
    print "REMAINING_BYTES = ",REMAINING_BYTES
    print "MAX_BYTES = ", num_files * max_filesize
    print "MIN_BYTES = ", num_files * min_filesize

    assert( REMAINING_BYTES < (num_files * max_filesize))
    assert(REMAINING_BYTES > (num_files * min_filesize))        

    print "num files = " , num_files
    for fileNumber in range(0, num_files):
        fileSize = randint(min_filesize, max_filesize)
        num_left_files = num_files - fileNumber
        # maxima condition
        if ( (REMAINING_BYTES - fileSize) > (num_left_files * max_filesize) ):
            fileSize = max_filesize
        # minima condition
        elif( (REMAINING_BYTES - fileSize) < ( num_left_files * min_filesize) ):
            fileSize = min_filesize
        fileArray.append(fileSize)
        REMAINING_BYTES -= fileSize

    return fileArray

if __name__ == "__main__":
    """ Main Start """

    arr = generateFileArray(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]))
    print arr

