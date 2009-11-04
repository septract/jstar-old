class Cell {
  void <init>() : { } { this.<Cell: int val> |-> _ };
  
  int get() : int X. 
  { this.<Cell: int val> |-> X} 
  { X=return * this.<Cell: int val> |-> X };

  void set(int x) : 
  { this.<Cell: int val> |-> _ } 
  { this.<Cell: int val> |-> x };
}
