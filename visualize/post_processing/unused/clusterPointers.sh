#This script clusters disk source pointers of the same type as 1 type. This helps us in clustering templates of destination blocks whose source blocks are of the same type.
#

# Input testfs1.struct.dict - dictionary containing structures. // this is an output of ./func_grab in func_var_parser
# Input dataStructureLayout.dict - file containing BLOCK:<block_num>:<off_start><off_end>:structName // this is an output of ./dataStructureGenerator in func_var_parser
# Input templates in templates/* folder. // these are outputs of ./createTemplate in post_proecessing folder
# Output replaces templates in templates/* folder that contain same source block pointers // this is done inplace


# XXX This algorithm will not work if dataStructureLayout.sh does not capture structure copy operations correctly.
# in other words, if dstruct_inode is written after being typecasted to (char *), there is NO_WAY we can find physical offset of internal block pointers 
# of dstruct inode

#Algorithm:
#	read the structure dictionary that was created by func_var_parser. this dictionary is of the form:
#	<structure_name>::<sub_element_name>:sub_element_type
#	check if sub_element_name is a array. if yes, obtain size of the array
#	create tuples of the form <structure_name> [4,5,6,7] [8,9,10,11] [12,13,14,15]
#	
#	read dataStructureLayout.dict. Get Block Number that contain structure name. get the following relationship
#	B<block_number> [4,5,6,7] [8,9,10,11] ... [41,42,43,44] [o1,o2,o3,o4]
#	
#	go through templates. replace these two instances: 
#		B[4,7] B[8,11] B[12-15] with B[o1,o4] 
#		B [4,5,6,7] B [o1,o2,o3,o4]
#

if [[ $# -lt 2 ]]; then
	echo "Usage ./clusterPointers.sh <structure_dictionary> <dataStructureLayout>"
fi

echo "automatically looking at templates inside templates/* folder"

STRUCT_DICT=$1
DATA_LAYOUT=$2

# XXX do something to extract size of NR_DIRECT_BLOCKS as 4
#while read line; do
#	subElementName=`echo $line | cut -d":" -f3`
#	`echo $subElementName | grep -b -o "\["`
#	if   
#done < $STRUCT_DICT
