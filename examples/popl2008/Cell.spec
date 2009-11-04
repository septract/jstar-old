import "Object.spec";

class Cell {
  define Val(x,content=y) as x.<Cell: int val> |-> y ;

  void <init>() : { } { Val$(this,{content=_ }) };
  
  int get() : 
  { Val$(this, {content=_X})} 
  { _X=return * Val$(@this:, {content=_X}) };

  void set(int x) : 
  { Val$(this, {content=_})} 
  { Val$(this, {content=x}) };
}

