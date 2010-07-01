#!/bin/bash
# Run soot and jStar on all the *.java files in a directory.

DEBUG=0 # set to nonzero to enable debug output

function usage () {
	printf "Usage: %s [-t target_dir] [-s soot_jar] [-r rt_jar] [-j jstar]\n" $0
	exit 1
}

# In the first phase we populate JSTAR_TARGET, SOOT_JAR, RT_JAR, and JSTAR.
# In the second phase we run Soot and jStar, using the above variables.

# The value of each configuration variable is taken from the command line.
# If not specified, then it is taken from the corresponding environment
# variable. If still not specified, a default is provided.
while getopts t:s:r:j: opt
do
	case $opt in
		t) JSTAR_TARGET="$OPTARG";;
		s) SOOT_JAR="$OPTARG";;
		r) RT_JAR="$OPTARG";;
		j) JSTAR="$OPTARG";;
		?) usage
	esac
done
if [ -z $JSTAR_TARGET ]; then
	JSTAR_TARGET="."
fi
if [ -z $SOOT_JAR ]; then
	SOOT_JAR=`locate soot | grep jar$ | head -1`
fi
if [ -z $RT_JAR ]; then
	RT_JAR=`which javac`
	RT_JAR=`readlink -f $RT_JAR`
	RT_JAR=`dirname $RT_JAR`
	RT_JAR=`dirname $RT_JAR`
	RT_JAR="$RT_JAR/jre/lib/rt.jar"
fi
if [ -z $JSTAR ]; then
	JSTAR="jstar"
fi
BAD_ENV=0
if [[ ! -d $JSTAR_TARGET ]]; then
	echo "Please provide a valid target. ($JSTAR_TARGET isn't)"
	BAD_ENV=1
fi
if [[ ! -f $SOOT_JAR ]]; then
	echo "Please tell me where soot's jar is. ($SOOT_JAR isn't good)"
	BAD_ENV=1
fi
if [[ ! -f $RT_JAR ]]; then
	echo "Please tell me where rt.jar is. ($RT_JAR isn't good)"
	BAD_ENV=1
fi
if [[ ! -x `which $JSTAR` ]]; then
	echo "Please tell me how to execute jstar. ($JSTAR isn't good)"
	BAD_ENV=1
fi
if (($BAD_ENV)); then
	exit 2
fi
if (($DEBUG)); then
	echo "JSTAR_TARGET=$JSTAR_TARGET"
	echo "SOOT_JAR=$SOOT_JAR"
	echo "RT_JAR=$RT_JAR"
	echo "JSTAR=$JSTAR"
fi

# Now we do the work in a subdirectory called jstar.out.
# Compile *.java classes, run soot on *.class files, and run jstar on *.jimple.
HERE=`pwd`
cd $JSTAR_TARGET
rm -rf jstar.out
mkdir jstar.out
javac *.java -d jstar.out
cd jstar.out
CLASSES=`find -name \*.class | sed 's/.class$//' | sed 's/^\.\///' | tr '/' '.'`
if (($DEBUG)); then
	echo "CLASSES=$CLASSES"
fi
java -jar $SOOT_JAR -cp .:$RT_JAR $CLASSES -f J -d .
for f in $CLASSES; do
	# TODO(rgrig): Make "specs", "logic", and "abs" configurable.
	$JSTAR -f $f.jimple -s ../specs -l ../logic -a ../abs
done
cd $HERE
