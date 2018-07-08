#!/bin/sh

# echo > $1

# a=0

# until [ $a -gt 10 ]
# do
#    echo "testing for synquid" | tee -a $1
#    a=`expr $a + 1`
#    python run_tests.py --sections succinct --synt | tee -a $1
# done

a=0

until [ $a -gt 10 ]
do
   echo "testing for succinct types" | tee -a $1
   a=`expr $a + 1` 
   python run_tests.py --sections succinct --synt --graph --succ | tee -a $1
done
