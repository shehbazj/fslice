# ******* Do not call this script directly ****************
# This script is called from createTemplate.sh. It creates checksum for each template and stores the ckecksum in checksums folder.
# each blocks checksum is stored in a separate file named after its block number.

file=$1
blockNumber=$2
removeConstants=$3
numLines=`wc -l ../templates/$file.template | cut -d" " -f1`
if [[ $removeConstants == True ]]; then
	sed -i "$numLines s/B$blockNumber/BC/g" ../templates/$file.template
fi
cksum ../templates/$file.template | cut -d' ' -f1 >> ../cksums/$blockNumber
#rm classifier/$file.template

