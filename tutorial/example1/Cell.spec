class Cell {
  void <init>() : { } { @this:.<Cell: int val> |-> y };
  
  int get() : 
  { @this:.<Cell: int val> |-> _X} 
  { _X=$ret_var * @this:.<Cell: int val> |-> _X };

  void set(int) : 
  { @this:.<Cell: int val> |-> _X } 
  { @this:.<Cell: int val> |-> @parameter0: };
}
