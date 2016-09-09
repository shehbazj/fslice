def elementIsVariable(element, blockContents):
        firstElementFieldSize = 0
        currentElementFieldSize = 0
	count = 0
	index = 0
        while index < len(blockContents):
                count = 0
                if blockContents[index] == element:
                        while index < len(blockContents) and blockContents[index] == element:
                                count += 1
                                index += 1
                        if firstElementFieldSize == 0:
                                firstElementFieldSize = count
				continue
                        else:
                                currentElementFieldSize = count
                                if firstElementFieldSize != currentElementFieldSize:
                                        return -1
		index += 1
        return firstElementFieldSize

def generateVariableStruct(blockContents):
        structure = []
        element = blockContents[0] # can be 'U' or 'P'
        count = elementIsVariable(element,blockContents)
        index = 0
        if count > 0: # element has constant size
                structure = elements * [count]
                index = count # scan from next element
        else:  # variable list
                structure.append(element + '*')
	
	print structure
	print count
	print index
        while index < len(blockContents): # get next elements size
                if blockContents[index] != element:
                        count = elementIsVariable(blockContents[index],blockContents)
                        if count > 0: # element has constant size
                                structure.extend( [blockContents[index]] * count)
                        else:
                                structure.append(blockContents[index] + '*')
			return structure 		
                index+=1
        return structure

if __name__ == "__main__":
        """ Main Start """
	
	blockContents = ['U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U']
	structure = generateVariableStruct(blockContents)
	print structure

#	count = elementIsVariable('P',['U', 'U', 'P', 'P', 'U', 'U', 'P', 'P', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'P', 'P', 'U', 'U', 'U', 'U', 'U', 'U', 'U', 'U'])
#	print count
