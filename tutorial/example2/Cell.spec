class Cell {
  define Val(x,content=y) = x.<Cell: int val> |-> y ;

  void <init>() : { } { Val$(@this:,{content=_z}) };
  
  int get() : 
  { Val$(@this:, {content=_X})} 
  { _X=$ret_var * Val$(@this:, {content=_X}) };

  void set(int) : 
  { Val$(@this:, {content=_X})} 
  { Val$(@this:, {content=@parameter0:}) };
}
