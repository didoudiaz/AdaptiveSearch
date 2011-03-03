#!/bin/sh

prefix=/tmp/all-interval-$$
tmp1=$prefix.1.log
tmp2=$prefix.2.log
tmp3=$prefix.3.log

rm -f $prefix*


prog=${1:-all-interval}
n=${2:-100}
nb_exec=${3:-100}
sleep=${4:-0}


dispCount () {
    sort $tmp2 | uniq >$tmp3
    nbdiff=`wc -l $tmp3 | cut -d ' ' -f 1`
    printf '%9d %9d %9d %9d\n' $1 $2 $3 $nbdiff
}



touch $tmp2
n1=`expr $n - 1`
triv1=0
triv2=0
notriv=0
i=0

echo '  exec no       #triv1    #triv2  #no-triv  #different'

while [ $i -lt $nb_exec ] ; do 
    sol=`$prog $n | tail -2 | head -1`
    echo $sol >>$tmp1
    set $sol
    if [ $1 = $n1 -a $2 = 0 ]; then
	triv1=`expr $triv1 + 1`
#	echo triv1: $sol
    elif [ $1 = 0 -a $2 = $n1 ]; then
	triv2=`expr $triv2 + 1`
#	echo triv2: $sol
    else
	notriv=`expr $notriv + 1`
#	echo notriv: $sol
	echo $sol >>$tmp2
    fi
    i=`expr $i + 1`
    printf 'exec %4d: ' $i
    dispCount $triv1 $triv2 $notriv
    sleep $sleep
done


#rm -f $prefix*
