import "Cell.spec";

class Recell {
  define Val(x,content=y;oldcon=z) as Val$Cell(x, {content=y}) * field(x, <Recell: int bak>, z) ;

  void <init>() : { } { Val$(this, {content=_x; oldcon=_z}) };
  
  int get() : 
  { Val$(this, {content=_X; oldcon=_Y})} 
  { _X=return * Val$(this, {content=_X; oldcon=_Y}) };

  void set(int x) : 
  { Val$(@this:, {content=_X; oldcon=_})} 
  { Val$(@this:, {content=x; oldcon=_X}) };
}
