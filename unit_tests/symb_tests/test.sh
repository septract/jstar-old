

for file in `ls *_test | sed "s/_test//"` 
do 
#  string="."
#  printf "%b" "$string" 
  test_symb  -f $file\_test -l $file\_logic -a $file\_abs; 
done