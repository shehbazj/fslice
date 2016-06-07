#!/usr/bin/python

# Cluster.py takes a bunch of files which have a list of checksums inside them, and merges the files if one or more checksums in
# either of the files matches. By default, the program takes all files from the folder cksums and then merges files


import sys
import shutil
import os

nextFile = 0
allFiles = []

def commonCksum(f1,f2):
	cksum1 = set(open(f1,'r'))
	cksum2 = set(open(f2,'r'))
#	if cksum1.issubset(cksum2) or cksum2.issubset(cksum1):
#		return True
#	return False
	if cksum1.isdisjoint(cksum2):
		return False
	return True

def getNextFile():
	global nextFile
	global allFiles
	if nextFile > (len(allFiles)-1):
		#print "returning none since nextFile = ",nextFile,"len of allFiles = ",len(allFiles)
		return None
	else:
		#print "returning ",nextFile,allFiles[nextFile]
		return allFiles[nextFile]	
	
if __name__ == "__main__":
    """ Main Start """
if len(sys.argv) > 1:
	allFiles=sys.argv[1:len(sys.argv)]
else:
# copy all files from cksums folder to current directory
	src_files=os.listdir("cksums")
	dest="."
	for file_name in src_files:
    		full_file_name = os.path.join("cksums", file_name)
    		if (os.path.isfile(full_file_name)):
        		shutil.copy(full_file_name, dest)
			allFiles.insert(len(allFiles),file_name)
#print allFiles

#print "f1 returned",f1
while True:
	f1=getNextFile()
	nextFile+=1
	while f1:
		f2=getNextFile()
		#print "f2 returned",f2
		if f2 is None:
			break
		if commonCksum(f1,f2) == True:
			#print f1,f2,"Match"
			f=f1+'.'+f2
			#print "name of f",f," after merging ",f1,f2
			mergeFile=open(f, "w")
			fileOne=open(f1,"r")
			fileTwo=open(f2,"r")
			mergeFile.write(fileOne.read())
			mergeFile.write(fileTwo.read())
			mergeFile.close()
			fileOne.close()
			fileTwo.close()
			os.remove(f1)
			os.remove(f2)
			allFiles.remove(f1)
			allFiles.remove(f2)
			allFiles.insert(0,f)		
			#print "all Files = ",allFiles
			f1=f
		else:
			nextFile+=1
			#print f1,f2,"No Match"
			#f1=f2
	if f1 is not None:
		pos = allFiles.index(f1)	
		if pos < 0 or pos > len(allFiles) -1:
			break
		else:
			nextFile = pos+1	
	else:
		break
#print allFiles
#print commonCksum(f1,f2)
