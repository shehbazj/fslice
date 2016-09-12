blockSize = 64
structSize = 4

def maxPtr(blockContents):
	maxPtrCount = 0
	for i in range( 0, blockSize, structSize):
	        structInstance = blockContents[i:i+structSize]
	        ptrCount = structInstance.count('P');
		print ptrCount
	        if ptrCount > maxPtrCount:
	                maxPtrStructInstance = structInstance
	                maxPtrCount = ptrCount
	#blockDSMap[blockNumber] = maxPtrStructInstance
	return maxPtrStructInstance

def getPtrIndex(blockContents):
        ptrList = []
        index = 0
        while index < blockSize:
                if blockContents[index] is 'U':
                        index+=1
                        continue
                if blockContents[index] is 'P':
                        ptrList.append(index)
                        while blockContents[index] is 'P' and index < blockSize:
                                index+=1
        return ptrList

if __name__ == "__main__":
        """ Main Start """
	
	blockContents = ['U', 'U', 'P', 'U', 'U', 'U', 'P', 'U', 'U', 'U', 'P', 'P', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U']
	structure = maxPtr(blockContents)
	print structure

	ptrIndex = getPtrIndex(blockContents)
	print ptrIndex
