#include "share/atspre_staload.hats"

fun triples () : stream_vt(@(int,int,int)) =
  aux1(1) where {
    vtypedef res_vt = stream_vt(@(int,int,int))
    fun aux1(z: int): res_vt = aux2(1, z)
    and aux2(x: int, z: int): res_vt =
          if x <= z then 
          aux3(x, x, z) 
          else aux1(z+1)
    and aux3(x: int, y: int, z: int): res_vt =
          $ldelay(
            if y <= z then
              (stream_vt_cons((x, y, z), aux3(x, y+1, z)))
            else !(aux2(x+1, z))
          )
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