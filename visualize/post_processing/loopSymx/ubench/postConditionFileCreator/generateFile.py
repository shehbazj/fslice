# generateFile.py [number of post Conditions, start range, end range]

# creates a linear file of the format
# 4
# 6
# 2
# 1
# when input given is <4, 1, 10>

import random
import sys


if __name__ == "__main__":
    if len(sys.argv) != 4:
        print "Usage: generateFile.py numPostConditions StartRange EndRange"
        sys.exit()
    
    numPostConditions = int(sys.argv[1])
    startRange = int(sys.argv[2])
    endRange = int(sys.argv[3])
    seed_numbers = []
    seed_numbers = random.sample(range ( startRange, endRange), numPostConditions)
    print seed_numbers

    f = open('randomFile', 'w')
    for i in range(0, numPostConditions):
        f.write(str(seed_numbers[i]) + "\n")
    f.close()
      
