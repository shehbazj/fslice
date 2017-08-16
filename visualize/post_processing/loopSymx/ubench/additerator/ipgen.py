# this program takes postConditionFile as an input.
# postConditionFile contains inputs 1 number in 1 line. these may be
# generated randomly and arranged in the form
# **postConditionFile **
#
# 2
# 31
# 13
# 3
# 
# *** array_size / iterator size**
# 
# attaches ipgen_header.py and fills body with expression of the form
# s.add(count1 * op1 + count2 * op2 == postConditionValue)
# s.add( count1 + count2 == array_size)
#
# attaches ipgen_footer.py
# generates all of this in ipgenConstAdd folder with names
# ipgenFile_postConditionNumber.py
#
#

import sys

if __name__ == "__main__":
    if len(sys.argv) != 3:
        print "Usage: ipgen.py postConditionFile array_size"
        sys.exit()
    
    postConditionFileName = sys.argv[1]
    arraySize = sys.argv[2]

    postConditionFile = open(postConditionFileName)
    postConditionValues = postConditionFile.read().splitlines()

    for postCondition in postConditionValues:
        postConditionFile = "gen_const_" + postCondition + ".py"

        f = open(postConditionFile, 'w')
    
        # write header     
        ipgenHeaderFile = open("ipgen_header")
        with open("ipgen_header") as ipgenHeaderFile:
            for line in ipgenHeaderFile:
                f.write(line)
    
        # write body

        for i in range(1, int(arraySize) + 1):
            f.write("    counter"+ str(i) +" =Int('counter"+ str(i) +"')\n")
            f.write("    op"+ str(i) +" =Int('op"+ str(i) +"')\n")
            f.write("    s.add(counter"+ str(i) +" >= 0)\n")
            f.write("    s.add(counter"+ str(i) +" <= 1)\n")

        f.write("    s.add(")
        for i in range(1, int(arraySize) - 1):
            f.write("    counter" + str(i) + " * " + str(i) + " + ")
        f.write("    counter" + arraySize + " == " + postCondition + ")\n")
        
        # write footer
        ipgenFooterFile = open("ipgen_footer")
        with open("ipgen_footer") as ipgenFooterFile:
            for line in ipgenFooterFile:
                f.write(line)
    
        ipgenHeaderFile.close()
        ipgenFooterFile.close()

        f.close()
    
