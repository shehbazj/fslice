"""
 annotation_benchmark.py
 This file generates a bunch of file system commands that create, read and write files and directories.
 
"""

import argparse
from collections import defaultdict
import re
from random import randint

cmd_mkdir= "mkdir "
cmd_change_directory = "cd "
cmd_create_file = "touch "
cmd_write_file = "write "
cmd_read_file = "read "

MAX_FILE_OR_DIR = 40
BLOCK_SIZE = 64

percent = 0
depth = 0
dir_percentage = 0  
min_filesize = 0
max_filesize = 0  
num_files = 0
files_in_each_directory = 0
file_number = 0
fileArray = []

def generateFileContents(size):
    s = ""
    while len(s) < size:
        for i in range(0,9):
            s+= str(i)
            if len(s) > size:
                break
    return s

def make_files():
    global file_number
    file_to_create = randint(1, files_in_each_directory)
    for fileNum in range(0,file_to_create):
        if file_number >= num_files:
            return
        fileName = 'file'+str(file_number)
        print cmd_create_file,fileName
        fileContent = generateFileContents(fileArray[file_number])
        print cmd_write_file+str(fileName)+' '+fileContent
        file_number+=1
        print cmd_read_file+str(fileName)
 

def make_directory(new_directory):
    print cmd_mkdir+new_directory

def change_directory(directory_name):
    print cmd_change_directory, directory_name
    if '..' in directory_name:
        return
    else:
        make_files() 
       

# returns an array with _num_of_partitions elements where sum of the elements is _sum
def getRandomNumbers(_sum, _num_of_partitions):
    arr = []
    #print _sum, _num_of_partitions
    if _sum < _num_of_partitions:
        while _num_of_partitions > 0:
            if _sum > 0:
                arr.append(1) 
                _sum -=1
            else:
                arr.append(0)
            _num_of_partitions -=1
        return arr
    else:
        arr.append(_sum - _num_of_partitions + 1)
        for elem in range(1, _num_of_partitions):
            arr.append(1)
        return arr

"""
    Generates an array of file sizes 
"""

def generateFileArray(min_filesize, max_filesize, num_files):

    availableBytes = (BLOCK_SIZE * 512 * percent ) / 100
    #print "Available Bytes " , availableBytes
    fileBytes = (availableBytes * (100 - dir_percentage)) / 100

    REMAINING_BYTES = fileBytes
    #print "REMAINING_BYTES = ",REMAINING_BYTES
    #print "MAX_BYTES = ", num_files * max_filesize
    #print "MIN_BYTES = ", num_files * min_filesize

    assert( REMAINING_BYTES < (num_files * max_filesize))
    assert(REMAINING_BYTES > (num_files * min_filesize))

    #print "num files = " , num_files
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

    parser = argparse.ArgumentParser()

    parser.add_argument('percent', type=int, default=30, nargs= '?', help="percentage filesystem")
    parser.add_argument('depth', type=int, default=3, nargs= '?', help="directory depth")
    parser.add_argument('dir_percentage', type=int, default=20, nargs= '?', help="dir percentage")
    parser.add_argument('min_filesize',type=int, default=20, nargs= '?', help="min_filesize")
    parser.add_argument('max_filesize',type=int, default=400, nargs= '?', help="max_filesize")
    
    args = parser.parse_args()

    percent = args.percent
    depth = args.depth
    dir_percentage = args.dir_percentage
    min_filesize = args.min_filesize
    max_filesize = args.max_filesize


    NUM_DIRS=int((MAX_FILE_OR_DIR * dir_percentage) / 100)
    num_files=(MAX_FILE_OR_DIR - NUM_DIRS)

    fileSizeArray = generateFileArray(min_filesize, max_filesize, num_files)

#    files_in_each_directory = (num_files + NUM_DIRS -1) / NUM_DIRS
#    if not files_in_each_directory:
#        files_in_each_directory = 1
    files_in_each_directory = 5
        
    if depth > NUM_DIRS:
        exit

    NUM_DIRS_LEFT = NUM_DIRS

    DIRNUM = 0
    DIRNAME = 'dir'+`DIRNUM`
    DEPTH = depth
    ROOT = "/"

    parentDir = ROOT

    print "Maximum Number of Files ", num_files
    print "Maximum Number of Directories ", NUM_DIRS
    print "Max Files in each Directory ", files_in_each_directory

    # make minimum number of directories to match depth

    while DEPTH > 0:
        make_directory(DIRNAME)
        change_directory(DIRNAME)
        parent_directory = DIRNAME
        DIRNUM+=1
        DIRNAME = 'dir'+`DIRNUM`
        NUM_DIRS_LEFT-=1
        DEPTH-=1

    # rewind
    DEPTH = depth
    while DEPTH > 0:
        change_directory('..')
        DEPTH -=1

    # create array that records number of directories at each depth
    directoryAtEachLevel = getRandomNumbers(NUM_DIRS_LEFT,depth)
    #print directoryAtEachLevel

    # for each level, make X number of directories, where X is element
    # at position X in directoryAtEachLevel

    level=0
    for numDirs in directoryAtEachLevel:
        #print "at level ", level, "number of directories required ", numDirs
        for directoryNumber in range(0,numDirs):
            dirname =  "dir"+`level`+`directoryNumber`
            make_directory(dirname)
        level += 1
        change_directory(dirname)
    
    #rewind
    DEPTH = depth
    while DEPTH > 0:
        change_directory('..')
        DEPTH -= 1

    ## Directory structure created
