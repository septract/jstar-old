import "Cell.spec";

class DCell {
  define Val(x,content=y) = y!=y ;
  define DVal(x,content=y) =  Val$Cell(x,{content=builtin_plus(y,y)}) ;

  void <init>() : { } { DVal$(@this:, {content = _w}) };

  int get() : 
  { Val$(this, {content=_X}) } 
  { _X=return * Val$(this, {content=_X})} 
 andalso
  { DVal$(this, {content=_X})} 
  { builtin_plus(_X,_X)=return * DVal$(this, {content=_X}) };

  void set(int x) : 
  { Val$(this, {content=_X}) }
  { Val$(this, {content=x}) } 
andalso
  { DVal$(@this:, {content=_X}) } 
  { DVal$(@this:, {content=x}) };
}
