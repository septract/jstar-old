export PWD=`pwd`
CLASSPATHSOOT=""
for i in *.jar; do CLASSPATHSOOT=$CLASSPATHSOOT:$PWD/$i; done
export CLASSPATHSOOT=$CLASSPATHSOOT
export CLASSPATH=$CLASSPATH:$CLASSPATHSOOT:/System/Library/Frameworks/JavaVM.framework/Classes/classes.jar:.


