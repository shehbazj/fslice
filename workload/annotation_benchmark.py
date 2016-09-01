"""
 annotation_benchmark.py
 This file generates a bunch of file system commands that create, read and write files and directories.
 
"""

import argparse
from collections import defaultdict
import re
from random import randint

"""
Filesystem specific commands.
"""

cmd_mkdir= "mkdir "
cmd_change_directory = "cd "
cmd_create_file = "touch "
cmd_write_file = "write "
cmd_read_file = "read "

"""
Global Variables.
"""

MAX_FILE_OR_DIR = 40
BLOCK_SIZE = 64

percent = 0
depth = 0
dir_percentage = 0  
dirnum = 0
min_filesize = 0
max_filesize = 0  
num_files = 0
num_files_in_directory = []
file_number = 0
fileArray = []
dir_entries = defaultdict(list)
dir_stack = []

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
#   TODO
#    file_to_create = randint(1, num_files_in_directory)
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
#    change_directory(new_directory)
#   make_files()
#    change_directory('..')

def change_directory(directory_name):
    print cmd_change_directory, directory_name

# returns an array with _num_of_partitions elements where sum of the elements is _sum
# The logic makes sure, there are no 0's in the middle of the resultant array
# This is because when we want to create variable number of directories at each level,
# we do not want 0 directories in the middle of a hierarchy.

def getRandomNumbers(_sum, _num_of_partitions):
    arr = []
    left_sum = _sum
    for elements in range(0,_num_of_partitions):
        if _sum > 1:
            candidate_num = randint(1,int(_sum/2))
        else:
            candidate_num = 1
        #print "candidate_num",candidate_num
        if(left_sum == 0):
        #    print "assigning 0"
            candidate_num = 0
        elif (left_sum - candidate_num) < 0:
        #    print "assigning ",left_sum, " since candidate num", candidate_num , " is greater"
            candidate_num = left_sum
        elif (elements == _num_of_partitions - 1): # last element
            candidate_num = left_sum
        arr.append(candidate_num)
        left_sum -= candidate_num
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

def generateMinimumDirectoryHierarchy():
    num_dirs_left = num_dirs
    global dirnum
    dirname = 'dir'+`dirnum`
    t_depth = depth
    ROOT = "/"

    parentdir = ROOT

    while t_depth > 0:
        make_directory(dirname)
        dir_entries[parentdir].append(dirname)
        change_directory(dirname)
        parentdir = dirname
        dirnum+=1
        dirname = 'dir'+`dirnum`
        num_dirs_left-=1
        t_depth-=1

    # rewind
    t_depth = depth
    while t_depth > 0:
        change_directory('..')
        t_depth -=1

def makeDirectories(parentDir):
    change_directory(parentDir)         
    if (len(dir_entries[parentDir])) is 0:
        change_directory('..')
        if len(dir_stack) is 0:
            return
        else:
            parentDir = dir_stack.pop()
            while parentDir is "M" and len(dir_stack) is not 0:
                change_directory('..')
                parentDir = dir_stack.pop()
            if len(dir_stack) is 0:
                return
            return makeDirectories(parentDir)
    else:
        dir_stack.append("M")
        for childDir in dir_entries[parentDir]:
            make_directory(childDir)
            dir_stack.append(childDir)
        parentDir = dir_stack.pop()
        return makeDirectories(parentDir)

def generateRestOfDirectoryHierarchy():

    # First, create a map of <parent_directory, children_directories>
    potentialParentDirs = ['/']
    for level in range(0, depth):
        newDirs = []
        for dirNum in range(0,directoryAtEachLevel[level]):
            parent_dir = potentialParentDirs[randint(0, len(potentialParentDirs)-1)]
            print "parent_dir ", parent_dir
            newDir = 'dir'+str(level)+str(dirNum)
            dir_entries[parent_dir].append(newDir) 
            newDirs.append(newDir)
        print "new Potential Dir ========> ", newDirs
        potentialParentDirs = newDirs

    for dirs,dirlist in dir_entries.items():
        print dirs,' => ' ,dirlist
    
    # Next, create directory structure with the dir_entries map, and use dir_stack stack
    
    makeDirectories('/')         



if __name__ == "__main__":
    """ Main Start """

    ## accept arguments

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

    # initialise variables

    num_dirs=int((MAX_FILE_OR_DIR * dir_percentage) / 100)
    num_files=(MAX_FILE_OR_DIR - num_dirs)

    fileSizeArray = generateFileArray(min_filesize, max_filesize, num_files)
    assert(depth < num_dirs)
    generateMinimumDirectoryHierarchy()

    num_dirs_left = num_dirs - depth - 1 # removing directories created by 
                                    # generateMinimumDirectoryHierarchy
    # create array that records number of directories at each depth
    directoryAtEachLevel = getRandomNumbers(num_dirs_left,depth)
    print directoryAtEachLevel

    generateRestOfDirectoryHierarchy()    
