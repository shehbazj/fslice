import sys
import argparse

parser = argparse.ArgumentParser(description='Generate statistics for a TestFS workload.')
parser.add_argument('--verbose', dest='VERBOSE', const=True, default=False,
                    nargs='?', help='Print debug information.')

args = parser.parse_args()

# Constants.
POINTER_SIZE = 4
BLOCK_SIZE = 64
INODE_SIZE = 32
INODE_BLOCK_START = 64
DIRECT_BLOCKS_PER_INODE = 4

info_per_dir_or_file = dict()
on_disk_pointers = set()
total_inodes = 0
data_block_start = 192


class Information:
    def __init__(self, size, inode_number, inode_offset, isDirectory=True):
        self.__size = size
        self.__inode_number = inode_number
        self.__inode_offset = inode_offset
        self.__direct_blocks = []
        self.__indirect_block = None
        self.__isDirectory = isDirectory
        self.__inode_numbers_starting_offset = set()

        if self.__isDirectory:
            assert (self.__size > 0)
            self.__update_inode_starting_offsets(4)
            self.__update_inode_starting_offsets(14)

    def addDirectBlock(self, block_number):
        self.__direct_blocks.append(block_number)

    def getTotalDirectBlocks(self):
        return len(self.__direct_blocks)

    def getTotalIndirectBlocks(self):
        if self.__indirect_block:
            return 1
        else:
            return 0

    def updateSize(self, size):
        self.__size = max(self.__size, size)
        self.__updateBlocks__()

    def increaseSize(self, size):
        assert self.__isDirectory
        self.__update_inode_starting_offsets(self.__size + POINTER_SIZE - 1)
        self.__size += size
        self.__updateBlocks__()

    def __update_inode_starting_offsets(self, offset):
        # Mark the specified offset as the starting point of an inode number.
        # struct dirent {
        #   int d_name_len;
        #   int d_inode_nr;
        # };
        self.__inode_numbers_starting_offset.add(offset)

    def calculate_directory_entry_pointers(self):
        global on_disk_pointers

        if not self.__isDirectory:
            return

        # For each offset marked as the starting offset of the inode number
        # associated with a directory entry, calculate the actual disk offset
        # where it is stored.
        for st_offset in sorted(self.__inode_numbers_starting_offset):
            for disk_offset in xrange(st_offset, st_offset + POINTER_SIZE):
                # The disk block is calculated based on the blocks that have been
                # allocated for the specified inode.
                disk_block = self.__direct_blocks[disk_offset / BLOCK_SIZE]
                on_disk_pointers.add((disk_block * BLOCK_SIZE) + (disk_offset % BLOCK_SIZE))

    def __updateBlocks__(self):
        global data_block_start

        # Calculate the number of blocks required for the specified file/directory.
        required_blocks = self.__size / BLOCK_SIZE
        if self.__size % BLOCK_SIZE != 0:
            required_blocks += 1

        # Calculate and store the on-disk blocks that will be
        # allocated for the specified file/directory.
        while len(self.__direct_blocks) < required_blocks:

            # If all direct block pointers are used, then a indirect block
            # must be allocated for the specified file/directory.
            if len(self.__direct_blocks) == DIRECT_BLOCKS_PER_INODE:
                assert (self.__indirect_block is None)
                self.__indirect_block = data_block_start
                data_block_start += 1

            self.__direct_blocks.append(data_block_start)
            data_block_start += 1

    def getSize(self):
        return self.__size

    def getInodeNumber(self):
        return self.__inode_number

    def getInodeOffset(self):
        return self.__inode_offset

    def getIndirectBlock(self):
        return self.__indirect_block

    def getDirectBlocks(self):
        return sorted(self.__direct_blocks)

    def isDirectory(self):
        return self.__isDirectory

    def __str__(self):
        return "\n\tSize: {}\n\tInode: {}\n\tInode offset: {}\n\tIndirect block: {}\n\tDatablocks: {}\n".\
            format(self.__size, self.__inode_number, self.__inode_offset, self.__indirect_block,
                   sorted(self.__direct_blocks))


def getInode():
    global total_inodes

    # Calculate the size of the inodes allocated so far.
    total_inode_size = (total_inodes * INODE_SIZE)

    # Calculate the offset of the new inode; it can take values
    # from the set {0, 32}.
    inode_offset = total_inode_size % BLOCK_SIZE

    # Calculate the block number where the new inode will be stored.
    inode_number = INODE_BLOCK_START + (total_inode_size / BLOCK_SIZE)

    # Increase the number of allocated inodes.
    total_inodes += 1

    return inode_number, inode_offset

if __name__ == "__main__":
    # Path to root directory.
    ROOT_PATH = "/"

    # Commands to ignore.
    commands_to_ignore = ["cat", "catr", "checkfs", "ls", "lsr"]

    # Initialize the current directory to be the root.
    current_directory = ROOT_PATH

    # Initialize the full path to the parent directory.
    path_to_parent = ROOT_PATH

    # Maintain a stack of directory names, in order to calculate the
    # current directory in case of 'cd' operations.
    directory_stack = []

    # The root directory contains two entries:
    # 2 * sizeof(int) + len(".") + 1
    # 2 * sizeof(int) + len("..") + 1
    root_inode_number, root_inode_offset = getInode()
    root_info = Information(21, root_inode_number, root_inode_offset)
    info_per_dir_or_file[current_directory] = root_info

    # Add the data block associated with the root directory.
    root_info.addDirectBlock(data_block_start)
    data_block_start += 1

    for input_line in sys.stdin:
        # Split the input line and strip the '\n' character
        # from the last argument.
        arguments = input_line.split(" ")
        arguments[-1] = arguments[-1].strip()
        cmd = arguments[0]

        if cmd == "write":
            # Calculate the absolute path to the specified file.
            path_to_file = path_to_parent + arguments[1]

            # Make sure that the file is already stored inside the dictionary.
            # A file must have already been created ('touch'), in order for the
            # write operation to proceed.
            assert (path_to_file in info_per_dir_or_file)

            # The 'write' command always writes some bytes at the beginning of the
            # file, i.e., it does not append new data.
            current_info = info_per_dir_or_file[path_to_file]
            current_info.updateSize(len(arguments[2]))
            # info_per_dir_or_file[path_to_file] = current_info

        elif cmd == "owrite":
            # Calculate the absolute path to the specified file.
            path_to_file = path_to_parent + arguments[1]

            # Make sure that the file is already stored inside the dictionary.
            # A file must have already been created ('touch'), in order for the
            # write operation to proceed.
            assert (path_to_file in info_per_dir_or_file)

            # The 'owrite' command writes some bytes starting from the specified offset.
            current_info = info_per_dir_or_file[path_to_file]
            current_info.updateSize(int(arguments[2]) + len(arguments[3]))
            # info_per_dir_or_file[path_to_file] = current_info

        elif cmd == "touch":
            # 'Touch' supports multiple file names.
            for i in xrange(1, len(arguments)):
                # Calculate the absolute path to the specified file.
                path_to_file = path_to_parent + arguments[i]

                # Make sure that the specified name does not already exist.
                assert(path_to_file not in info_per_dir_or_file)

                # Calculate and store the information related to the newly created file.
                file_inode_number, file_inode_offset = getInode()
                file_info = Information(0, file_inode_number, file_inode_offset, False)
                info_per_dir_or_file[path_to_file] = file_info

                # Make sure that the parent directory already exists.
                assert(path_to_parent in info_per_dir_or_file)

                # Every file creation results in a new directory entry.
                # len(d_entry) = 2 * sizeof(int) + len(filename) + 1.
                parent_info = info_per_dir_or_file[path_to_parent]
                parent_info.increaseSize(9 + len(arguments[i]))
                # info_per_dir_or_file[path_to_parent] = parent_info

        elif cmd == "mkdir":
            # Make sure that the directory name ends with '/'.
            if arguments[1][-1] != '/':
                arguments[1] += '/'

            # Verify that the specified directory does not already exist.
            path_to_file = path_to_parent + arguments[1]
            assert (path_to_file not in info_per_dir_or_file)

            # Each directory contains two entries:
            # 2 * sizeof(int) + len(".") + 1
            # 2 * sizeof(int) + len("..") + 1
            dir_inode_number, dir_inode_offset = getInode()
            directory_info = Information(21, dir_inode_number, dir_inode_offset)
            info_per_dir_or_file[path_to_file] = directory_info

            # Add the data block associated with the newly created directory.
            directory_info.addDirectBlock(data_block_start)
            data_block_start += 1

            # Verify that the parent directory has already been created.
            assert (path_to_parent in info_per_dir_or_file)

            # Every directory creation results in a new directory entry.
            # len(d_entry) = 2 * sizeof(int) + len(filename) + 1.
            parent_info = info_per_dir_or_file[path_to_parent]
            parent_info.increaseSize(9 + len(arguments[1]))
            # info_per_dir_or_file[path_to_parent] = parent_info

        elif cmd == "cd":
            if arguments[1] == "." or arguments[1] == "./":
                continue

            if arguments[1] == ".." or arguments[1] == "../":
                # The current directory will be equal to the directory
                # that was inserted last into the stack.
                if path_to_parent == ROOT_PATH:
                    continue
                
                current_directory = directory_stack.pop()
            else:
                # Make sure that the directory name ends with '/'.
                if arguments[1][-1] != '/':
                    arguments[1] += '/'

                # Make sure that the directory exists.
                if arguments[1] == "/":
                    path_to_file = arguments[1]
                else:
                    path_to_file = path_to_parent + arguments[1]
                assert(path_to_file in info_per_dir_or_file)

                # Add the current directory to the directory stack.
                if arguments[1] == "/":
                    directory_stack = []
                else:
                    directory_stack.append(current_directory)

                # Mark the specified directory as the current directory.
                current_directory = arguments[1]

            # Update the absolute path to the parent directory.
            path_to_parent = ''.join(directory_stack) + current_directory

        else:
            # Check if the specified command is acceptable.
            if cmd in commands_to_ignore:
                continue

            print "Unknown command: {}\nExiting...".format(cmd)
            sys.exit(-1)

    # The number of inodes equals to the number of files and directories (keys)
    # stored inside the dictionary.
    stored_inodes = len(info_per_dir_or_file.keys())
    assert (stored_inodes == total_inodes)

    # The superblock contains 5 integer fields that are used as
    # on-disk pointers.
    total_direct_pointers = 5
    total_indirect_pointers = 0

    # Calculate the number of direct and indirect blocks as stored inside
    # the corresponding classes of information. This calculation is mostly
    # used for verification purposes.
    total_direct_blocks = 0
    total_indirect_blocks = 0

    # Calculate the number of files and directories.
    total_files = 0
    total_directories = 0

    for entry, info in info_per_dir_or_file.iteritems():
        if info.isDirectory():
            total_directories += 1
        else:
            total_files += 1

        # If the size of the file is larger than 4 * BLOCK_SIZE
        # then, an indirect block will be used.
        if info.getSize() > (4 * BLOCK_SIZE):
            total_indirect_pointers += 1

        # Count one direct pointer per BLOCK_SIZE bytes.
        for i in xrange(0, info.getSize(), BLOCK_SIZE):
            total_direct_pointers += 1

        # Update the number of direct and indirect blocks.
        total_direct_blocks += info.getTotalDirectBlocks()
        total_indirect_blocks += info.getTotalIndirectBlocks()

        # Calculate and store all on-disk pointers. Initially, for each
        # direct block pointer, mark the specified bytes as on-disk pointers.
        on_disk_offset = (info.getInodeNumber() * BLOCK_SIZE) + (info.getInodeOffset() + 12)
        total_datablocks = info.getTotalDirectBlocks()
        i = 0
        while i < total_datablocks and i < DIRECT_BLOCKS_PER_INODE:
            for j in xrange(0, POINTER_SIZE):
                on_disk_pointers.add(on_disk_offset + j)

            i += 1
            on_disk_offset += POINTER_SIZE

        # If an indirect block is also allocated, then mark the corresponding
        # bytes stored in that block as on-disk pointers.
        if total_datablocks > DIRECT_BLOCKS_PER_INODE:
            # Mark the bytes representing the indirect block as on-disk pointers.
            for j in xrange(0, POINTER_SIZE):
                on_disk_pointers.add(on_disk_offset + j)

            # Update the offset to point to the indirect block.
            on_disk_offset = info.getIndirectBlock() * BLOCK_SIZE
            bytes_used_in_indirect_block = (total_datablocks - DIRECT_BLOCKS_PER_INODE) * POINTER_SIZE

            for i in xrange(0, bytes_used_in_indirect_block):
                on_disk_pointers.add(on_disk_offset + i)

        # If the entry is a directory, then count the inode number of each directory
        # entry as an on-disk pointer.
        info.calculate_directory_entry_pointers()

    # There is at least direct pointer for the '/' (root) directory.
    assert(total_direct_pointers > 5)
    assert(total_indirect_pointers == total_indirect_blocks)
    assert(total_direct_pointers == (total_direct_blocks + 5))

    # The superblock contains 5 integer fields that are used as on-disk pointers.
    for offset in xrange(0, 5 * POINTER_SIZE):
        on_disk_pointers.add(offset)

    # Verify that the calculated number of on-disk pointers is correct.
    total_on_disk_pointers = len(on_disk_pointers)
    assert ((total_on_disk_pointers % POINTER_SIZE) == 0)
    total_on_disk_pointers /= POINTER_SIZE
    #   assert (total_on_disk_pointers == (total_direct_pointers + total_indirect_pointers))

    # The following statement must be executed only if the processing script
    # also considers inode numbers inside directory entries as on-disk pointers.
    assert ((total_direct_pointers + total_indirect_pointers + total_files +
             (total_directories * 3) - 1) == total_on_disk_pointers)

    print "Statistics:"
    if args.VERBOSE:
        width = 25
        for entry, info in info_per_dir_or_file.iteritems():
            sys.stdout.write(entry)
            for i in xrange(0, width - (len(entry))):
                sys.stdout.write(' ')

            print "{}".format(str(info))

    print "  -- Total on-disk pointers: {}".format(total_on_disk_pointers)

    if args.VERBOSE:
        print "  -- Total inodes: {}".format(total_inodes)
        print "  -- Total directories: {}".format(total_directories)
        print "  -- Total files: {}".format(total_files)
        print "  -- Total direct blocks: {}".format(total_direct_blocks)
        print "  -- Total direct pointers: {}".format(total_direct_pointers)
        print "  -- Total indirect blocks: {}".format(total_indirect_blocks)
        print "  -- Total indirect pointers: {}".format(total_indirect_pointers)
        print "  -- On-disk pointers: {}".format(sorted(on_disk_pointers))
