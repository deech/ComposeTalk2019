#include "share/atspre_staload.hats"

fun triples () : stream_vt(@(int,int,int)) =
  f1(1) where {
    vtypedef res = stream_vt(@(int,int,int))
    fun f1(z: int): res = f2(1, z)
    and f2(x: int, z: int): res =
          if x <= z then 
          f3(x, x, z) 
          else f1(z+1)
    and f3(x: int, y: int, z: int): res =
          $ldelay(
            if y <= z then
              (stream_vt_cons((x, y, z), f3(x, y+1, z)))
            else !(f2(x+1, z))
          )
  }

fun number_stream(start:int): stream_vt(int) = 
  loop(start) where {
    fun loop(curr:int):stream_vt(int) =
      $ldelay(stream_vt_cons(curr,loop(curr+1)))
  }

implement
main0(argc,argv) = let
//
#define N 100000
//
  val ts =
  stream_vt_filter_fun
  ( triples(),
    lam(ts) => let val (x, y, z) = ts in x*x + y*y = z*z end
  )
  val ts = stream_vt_takeLte(ts, N)
in
(
  stream_vt_con_free
  (stream_vt_foreach<(int, int, int)>(ts))
) where
{
  implement
  stream_vt_foreach$fwork<@(int,int,int)><void>(t,env) =
          let
            val (x, y, z) = t
          in
            println!(x, "," , y , "," , z)
          end
}
end // end of [main0]
