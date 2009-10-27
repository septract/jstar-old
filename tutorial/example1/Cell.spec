class Cell {
  void <init>() : { } { this.<Cell: int val> |-> _ };
  
  int get() : 
  { this.<Cell: int val> |-> _X} 
  { _X=return * this.<Cell: int val> |-> _X };

  void set(int x) : 
  { this.<Cell: int val> |-> _ } 
  { this.<Cell: int val> |-> x };
}
