class Cell {
  void <init>() : { } { @this:.<Cell: int val> |-> _ };
  
  int get() : 
  { @this:.<Cell: int val> |-> _X} 
  { _X=$ret_var * @this:.<Cell: int val> |-> _X };

  void set(int) : 
  { @this:.<Cell: int val> |-> _ } 
  { @this:.<Cell: int val> |-> @parameter0: };
}
