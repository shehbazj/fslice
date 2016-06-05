import itertools
import sys

labelId = 0
removeConstants = None

def num_to_taint_object(str):
	return getattr(sys.modules[__name__], str)


def V( a, b):
	return a;

def operate(op, op1, op2):
	if op is "add":
		return op1 + op2
	elif op is "mul":
		return op1 * op2
	elif op is "sdiv":
		return op1 / op2
	elif op is "udiv":
		return op1 / op2
	else:
		print "Undefined Binary Operation"

def generateLabel(op,op1,op2):
	global labelId
	labelId+=1
	label = "L"+str(labelId)
	if removeConstants is True:
		if isinstance(op1,int):
			op1 = 'C'
		if isinstance(op2,int):
			op2 = 'C'
	print label,op,op1,op2
	return label

def A( op, op1, op2, discard):
	global labelId
	if isinstance(op1,int) and isinstance(op2,int):
		return operate(op, op1, op2)

	elif isinstance(op1,basestring) and isinstance(op2,int):
		if op2 == 0:
			#print op1
			return op1
		return generateLabel(op,op1,op2)

	elif ((isinstance(op1,basestring) and isinstance(op2,list)) or
	(isinstance(op1,list) and isinstance(op2,basestring)) or
	(isinstance(op1,list) and isinstance(op2,list))):
		return generateLabel(op,op1,op2)
		
	elif isinstance(op1,list) and isinstance(op2, int):
		#if op2 == 0:
		#	print "returning ",op1
		#	return op1
		#print op,op1,op2
		mylist = []
		mylist.append(op)
		mylist.append('B')
		mylist.append(op1[-1])  # add block number
		mylist.append(op1[0])	# add block start
		mylist.append(op1[-2])	# add block end
		if removeConstants is True:
			mylist.append('C')
		else:
			mylist.append(op2)	# add op2
		labelId+=1
		label = "L" + str(labelId)
		print label,mylist
		return label
	else:
		print "No case matched for",op,op1,op2
		return []

# returns list containing all indexes block number and block taint

def B( bsize, bnum, bsizeTaint, bnumTaint, discard):
	#print 'B [',str(bnum),']'
	mylist = []
	for i in range(0,bsize):
		mylist.append(i)
	mylist.append(bnum)
	#print mylist
	print "B"+str(bnum),bnumTaint
	return mylist

# returns list of indexes and block number

def O(*arg):
	mylist = []
	for name in range(2,len(arg)):
		mylist.append(arg[name])
	mylist.append((arg[0])[-1])	# append block number
	return mylist

if __name__ == "__main__":
    """ Main Start """

removeConstants=True
# main()
t1=V(0, 1) # Taint<1, 0, 0>
# testfs_init_super_block()
t4=V(64, 4) # Taint<4, 0, 0>
# read_blocks()
t8=A("add",t1,t1, 8)
t9=B(64,0,t4,t8, 9) # GetBlock(64, 0)
# bitmap_getdata()
t33=O(t9,33,t9[4],t9[5],t9[6],t9[7]) # Load(13557972, 4)
# read_blocks()
t36=A("add",t33,t1, 36)
t37=B(64,2,t4,t36, 37) # GetBlock(64, 2)
