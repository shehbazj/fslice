import sys

from random import randint

scanList = [0, 1, 0, 0, 4, 5, 0, 0, 8, 9, 10, 11, 0, 0, 0, 0, 16, 17, 0, 0, 20, 21, 22, 23, 24, 0, 26, 0, 28, 29, 30, 0, 0, 33, 34, 35, 0, 0, 38, 0, 40, 41, 42, 0, 0, 0, 0, 47, 0, 0, 50, 51, 52, 53, 0, 0, 56, 57, 0, 59, 60, 0, 62, 0, 0, 65, 0, 67, 68, 69, 0, 0, 72, 0, 74, 75, 76, 77, 0, 0, 0, 0, 0, 0, 84, 0, 0, 0, 0, 0, 0, 0, 92, 0, 94, 0, 0, 97, 0, 0, 100, 0, 102, 103, 104, 0, 106, 0, 108, 0, 110, 0, 0, 0, 0, 115, 116, 0, 0, 0, 120, 0, 122, 123, 124, 125, 0, 127, 0, 129, 0, 0, 132, 0, 134, 0, 0, 137, 138, 139, 0, 0, 0, 143, 0, 0, 146, 0, 148, 149, 0, 151, 0, 153, 0, 0, 0, 0, 0, 159, 0, 161, 0, 0, 0, 165, 166, 0, 0, 169, 0, 171, 0, 173, 0, 175, 176, 0, 178, 179, 0, 181, 182, 0, 184, 185, 0, 187, 0, 189, 190, 0, 192, 193, 194, 0, 196, 0, 198, 0, 0, 0, 202, 0, 204, 205, 206, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

postCondition = 115

def getFit(x , y):
    maxval = max(x , y)
    minval = min(x , y)
    return maxval - minval

def getPos( currentIndex, direction, listsize):
    if direction == 0:
        if currentIndex < listsize - 1:
            print "return after increment ", direction, currentIndex + 1
            return (direction, currentIndex+1)
        else:
            print " no increment "
            return (not(direction), currentIndex)
    if direction == 1:
        if currentIndex > 0:
            print " return after decrement ", direction, currentIndex - 1
            return (direction, currentIndex-1)
        else:
            print " no decrement "
            return (not(direction), currentIndex)

# returns list
# takes list and scans it scanCount times or till fitness = 0
# returns smoothened list

def scan1(x , scanCount):
    direction = 0
    for i in range(scanCount):
        print "SCANCOUNT ", i , " LIST " , x
        index = 0
        while True:
            recv_direction, index = getPos(index, direction, len(x))
            if recv_direction != direction:
                break
            currentFit = getFit(sum(x), postCondition)
            if x[index] == 0:
                if getFit(sum(x) + index, postCondition) < currentFit:
                    print "new fitness with element ", getFit(sum(x) + index, postCondition)
                    x[index] = index
                else:
                    print "new fitness with element ", getFit(sum(x) + index, postCondition), " greater than current Fitness ", currentFit
                    
            if x[index] != 0:
                if getFit(sum(x) - x[index], postCondition) < currentFit:
                    print "new fitness without element ", getFit(sum(x) + index, postCondition)
                    x[index] = 0
                else:
                    print "new fitness with element ", getFit(sum(x) + index, postCondition), " less than current Fitness ", currentFit
            if getFit(sum(x), postCondition) == 0:
                return x
    return x
        
 
if __name__ == "__main__":
        scanList = scan1(scanList, 30)
        if getFit(sum(scanList), postCondition) == 0:
            print "SMOOTH",scanList
            sys.exit() 
        else:
            print "SOLUTION NOT SMOOTH ", scanList, getFit(sum(scanList), postCondition)
