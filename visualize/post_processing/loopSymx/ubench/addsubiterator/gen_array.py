#   genArray.py -

#   this program tries to generate different iterator operations based on 
#   iterator values and operation definitions to transform a pre-condition to a post-condition.

#   a genetic algorithm based on readings from
#   https://www.tutorialspoint.com/genetic_algorithms/genetic_algorithms_parent_selection.htm

#   takes start iterator value
#   end iterator value (if exists)
#   operation(s) per iteration - add i / subtract i
#   pre-condition = counter = 0
#   post-condition = counter = 75

#   create population
#   fitness function
#   parent selection
#   cross-over / mutation (do only mutation)
#   survivor selection
#   termination condition
#   lifetime adaptation

#   take inputs
#   takes start iterator value  - start
#   end iterator value (if exists) - end
#   iterator operation - itOp
#   operation(s) per iteration - add i / subtract i [operations +it -it]
#   pre-condition = counter = 0 - precond
#   post-condition = counter = 75   - postCond

import sys
import random
from random import randint
from collections import namedtuple


##Chromosome = namedtuple('Chromosome', "age fitness chromosome")
#
#class Chromosome():
#    def __init__(self):
#        self.age = 0
#        self.fitness = 0
#        self.chromosome = []
#    def __init__(self,age,fitness,chromosome):
#        self.age = age
#        self.fitness = fitness
#        self.chromosome = chromosome


def getPos( currentIndex, direction, listsize):
    if direction == 0:
        if currentIndex < listsize - 1:
     #       print "return after increment ", direction, currentIndex + 1
            return (direction, currentIndex+1)
        else:
    #        print " no increment "
            return (not(direction), currentIndex)
    if direction == 1:
        if currentIndex > 0:
     #       print " return after decrement ", direction, currentIndex - 1
            return (direction, currentIndex-1)
        else:
      #      print " no decrement "
            return (not(direction), currentIndex)

# returns list
# takes list and scans it scanCount times or till fitness = 0
# returns smoothened list

def scan(x , scanCount):
    direction = 0
    for i in range(scanCount):
    #    print "SCANCOUNT ", i , " LIST " , x
        index = 0
        while True:
            recv_direction, index = getPos(index, direction, len(x))
            if recv_direction != direction:
                break
            currentFit = getFit(sum(x), postCondition)
            if x[index] > 0:
                if getFit(sum(x) + (-2 * x[index]), postCondition) < currentFit:
#                    print "new fitness with element ", getFit(sum(x) + index, postCondition)
                    x[index] = (-1 * x[index])
 #               else:
  #                  print "new fitness with element ", getFit(sum(x) + index, postCondition), " greater than current Fitness ", currentFit
                    
            else:
                if getFit(sum(x) + (2 * x[index]), postCondition) < currentFit:
   #                 print "new fitness without element ", getFit(sum(x) + index, postCondition)
                    x[index] = (-1 * x[index])
    #            else:
    #                print "new fitness with element ", getFit(sum(x) + index, postCondition), " less than current Fitness ", currentFit
            if getFit(sum(x), postCondition) == 0:
                return x
    return x
       
 


# how close is the chromosome sum to postCondition sum
def getFit(x , y):
    maxval = max(x , y)
    minval = min(x , y)
    return maxval - minval

def mate (x = [] , y =[]):
    child_chromosome = []
    for i in range(0,len(x)):
        randgene = randint(0,1)
        if randgene:
            child_chromosome.append(x[i])
        else:
            child_chromosome.append(y[i])
    return child_chromosome

def getOldManIndex(age):
    return age.index(min(age))

def getMostFitGuyIndex(population, postCondition):
    minimum = getFit(sum(population[0]), postCondition)
    minindex = 0
    for i in range(1, len(population) -1):
        if minimum > getFit(sum(population[i]), postCondition):
            minimum = getFit(sum(population[i]), postCondition)
            minindex = i
    return minindex

def getLeastFitGuyIndex(population, postCondition):
    maximum = getFit(sum(population[0]), postCondition)
    maxindex = 0
    for i in range(1, len(population) -1):
        if maximum < getFit(sum(population[i]),postCondition):
            maximum = getFit(sum(population[i]), postCondition)
            maxindex = i
    return maxindex



if __name__ == "__main__":
#    if len(sys.argv() != 8):
#        print "HELP"    
#        print "#   takes start iterator value  - it_start"
#        print "#   end iterator value (if exists) - it_end"
#        print "#   iterator operation - itOp (inc1, dec1)"
#        print "#   operation(s) per iteration - add i / subtract i [operations +it -it]"
#        print "#   pre-condition = counter = 0 - precond"
#        print "#   post-condition = counter = 75   - postCond"
#        sys.exit(0)
   
#   create population
#   uses start value, end value (-1 means create till post_condition)
#   start and end value determine array size
#   iterator operation - determines the value inside the array.
#   pre-condition - determines first value and all other values.
#   eg. if it is 0, the values are 0 , (0 + it) * (itOperation1 | itOperation2 ) , 
#   (0 + it+1) * (itOperation1 | itOperation2 ) , ( 0 + it +2) * (itOperation1 | itOperation2) 
#   till it_end or till value decided -1.
    
    it_start = 0 #sys.argv[1]  # start iterator value (0)
    it_end = int(sys.argv[2])    # end iterator value    (75)
    itOp = 1  #sys.argv[3]  # inc1, dec1    (inc11)
#    itOperations =   # {'add', 'sub'}
    preCondition = 0
    postCondition = int(sys.argv[1])

    generation_begin = 1
    generation_end = 1000
    mutation_chromosome_count = 5
    mutation_gene_count = 5
    age_limit = 10
    mutationTrigger = 10

    crossover_count = 10
    population_size = 400

##################################################################################

#   population - initial values
#   itOperation1 , itOperation1 , itOperation1 , ... itOperation1_end
#   itOperation2 , itOperation2 , itOperation2 , ... itOperation2_end
#   (itOperation1 | itOperation2) (0,1) || (itOperation1 | itOperation2) (0,1) || ...

#   twod_list = []                                       \                      
#   for i in range (0, 10):                               \
#       new = []                  \ can be replaced        } this too
#       for j in range (0, 10):    } with a list          /
#           new.append(foo)       / comprehension        /
#       twod_list.append(new) 

    arrsize =  it_end - it_start
    population = []      
    for i in range ( 0, population_size):
        chromosome = []
        for j in range ( 0 , arrsize):
            choice = randint(0,1)
            itOperations = [j , -j]
            chromosome.append(itOperations[choice])
        population.append(chromosome)
    # add some generic operations as well
    
    # all operations of 1 iteration
    chromosome = []
    for i in range (0 , arrsize):
        chromosome.append(i)
    population.append(chromosome)
               
    # all operations of 1 iteration
    chromosome = []
    for i in range (0 , arrsize):
        chromosome.append(-i)
    population.append(chromosome)
    
#    # add operations till <= postCondition 
#    chromosome = []
#    for i in range (0 , arrsize):
#        if(i >= postCondition):
#            break
#        chromosome.append(-i)
#    chromosome.append((arrsize - i) * [0])
#    population.append(chromosome)

    print "=== POPULATION INITIALIZATION === "

    #   fitness function
    #   (sum - end_value) = minimum - assign ranks to each of the population.
    #   keep track of the fitness.

#    for i in range ( 0, len(population)):
#        print "chromosome ", i , ' -> ' , population[i], getFit(sum(population[i]), postCondition)
     
####################################################################################

    age = len(population) * [ 1 ] # gets updated after every iteration

    generation_no = generation_begin
    while ( generation_no < generation_end ):

    #   cross-over
    #   choose 2 random people over 10 iterations. cross. if cross has better fitness, replace
    #   one of the parents randomly.

        for i in range(0, crossover_count):

            parent1Index = randint(0, len(population) - 1)
            parent1 = population[parent1Index]
            parent1Fitness = getFit(sum(parent1), postCondition)

            parent2Index = randint(0, len(population) - 1)
            parent2 = population[parent2Index]
            parent2Fitness = getFit(sum(parent2), postCondition)

    #   XXX BUG. update child on each iteration
            child = mate(parent1, parent2)

    #   mutation
    #   change from itOperation1 to itOperation2 at 5 random points such that score converges.
        noUpdate = 0
        mutation_chromosome = []
        for mutation_chromosome_index in range( 0, min(mutation_chromosome_count, len(population))):

                # perform mutation
                mutation_chromosome_index = randint(0, len(population) - 1)
                mutation_chromosome = population[mutation_chromosome_index]            
                pre_mutation_fitness = getFit(sum(population[mutation_chromosome_index]), postCondition)
 #               print "BEFORE chromosome ", mutation_chromosome_index, " -> " , mutation_chromosome 
                for mutation_gene_index in random.sample(range( 0 , arrsize - 1), mutation_gene_count):
                    mutation_chromosome[mutation_gene_index] = mutation_chromosome[mutation_gene_index] * -1
            
  #              print "AFTER chromosome ", mutation_chromosome_index, " -> " , mutation_chromosome
            
                post_mutation_fitness = getFit(sum(mutation_chromosome), postCondition)
                
                # check if convergent
                if(pre_mutation_fitness < post_mutation_fitness):
#                    print "PREMUTATION FITNESS ", pre_mutation_fitness , " LESS POST MUTATION FITNESS " , post_mutation_fitness, " NO UPDATE"
                    noUpdate+= 1
                else:
#                    print "PREMUTATION FITNESS ", pre_mutation_fitness , " GREATER THAN POST MUTATION FITNESS " , post_mutation_fitness, " UPDATED"
                    population[mutation_chromosome_index] = mutation_chromosome
                    age[mutation_chromosome_index] = generation_no
        if noUpdate == mutation_chromosome_count:
            mutationTrigger-= 1
            # no change, spice it up a little bit
            randomPopulationMutexIndex = randint(0, len(population) - 1) 
            population[randomPopulationMutexIndex] = mutation_chromosome
            age[mutation_chromosome_index] = generation_no
#            
#
#                    
#        print "GENERATION ", generation_no , " END"
#        for i in range ( 0, len(population)):
#            print "chromosome ", i , ' -> ' , population[i] , " Fitness " , fitness[i] , " Age " , age[i]
#
#    #   survivor selection
#    #   remove one of the three
#    #   kill child, kill old man, kill least fit guy.
#
        oldmanIndex = getOldManIndex(age)
        leastFitGuyIndex = getLeastFitGuyIndex(population, postCondition)
    
        killwho = random.sample(range(1,3),1)
        killwho = 2
       
        if killwho == 1:
            population[oldmanIndex] = child
            age[oldmanIndex] = generation_no
        elif killwho == 2:
            population[leastFitGuyIndex] = child
            age[leastFitGuyIndex] = generation_no
        # FOR 3 KILL CHILD                  

        generation_no += 1
#        if mutationTrigger == 0:
#            print "MUTATION TRIGGERED AT ", generation_no 
#            break

    for i in range(0, len(population)):
        if (getFit(sum(population[i]), postCondition) == 0):
            print "FOUND: " , population[i]
            print "GENERATION: ", generation_no
            print "MIN FITNESS" , getFit(sum(population[getMostFitGuyIndex(population,postCondition)]), postCondition)
            exit
    print "GENERATION: ", generation_no
    print "MIN FITNESS" , getFit(sum(population[getMostFitGuyIndex(population,postCondition)]), postCondition)
    print "CHROMOSOME = ", population[getMostFitGuyIndex(population, postCondition)]


    sortPath = [[]]

    for i in range(0,len(population)):
        for j in range ( i, len(population)):
            if(getFit(sum(population[i]), postCondition) > getFit(sum(population[j]), postCondition)):
                a , b = population[i] , population[j]
                population[j], population[i] = a, b

#    for i in range(0, len(population)):
    for i in range(0, 5):
        print "postCondition = " , postCondition 
        print "ERROR ",getFit(sum(population[i]),postCondition) , "ACTUAL VALUE " , sum(population[i])
 #       print population[i]
 #       for j in range( 0, 5):
 #           print population[i][j], " * count" , j, " + "

##################################################################################
###################################    localMinima      ##########################
    
    
    for i in range(0, 5):
        scanList = population[i]
        print "CALLING SCAN ON ", scanList, " FITNESS = ", getFit(sum(scanList),postCondition)
        scanList = scan(scanList, 400)
        if getFit(sum(scanList), postCondition) == 0:
            print "SMOOTH",scanList
            sys.exit() 

    

##   termination condition
#
