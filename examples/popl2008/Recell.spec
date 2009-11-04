import "Cell.spec";

class Recell {
  define Val(x,content=y;old=z) as Val$Cell(x, {content=y}) * field(x, <Recell: int bak>, z) ;

  void <init>() : { } { Val$(this, {content=_x; old=_z}) };
  
  int get() : 
  { Val$(this, {content=_X; old=_Y})} 
  { _X=return * Val$(this, {content=_X; old=_Y}) };

  void set(int x) : 
  { Val$(@this:, {content=_X; old=_})} 
  { Val$(@this:, {content=x; old=_X}) };
}
