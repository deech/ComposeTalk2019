#include "share/HATS/temptory_staload_bucs320.hats"
#staload UN = "libats/SATS/unsafe.sats"

fun{a:vtflt} ptr_set
  {l:addr}
  (pf: !a? @ l >> a @ l | p: ptr l, x: a): void =
    !p := x

datavtype arr(a:vtflt,addr,int) = 
 | {l:addr}
   arr_nil(a,l,0) of ()
 | {l:addr}{n:nat}
   arr_cons(a,l,n+1) of (a,arr(a,l+sizeof(a),n)) 

prfun arr_split
  {a:vtflt}
  {l:addr}
  {n:int}{i:nat | i <= n}
  .<i>.
  (pf_arr: arr (INV(a), l, n)) :
    @(arr (a, l, i), arr (a, l+i*sizeof(a), n-i)) =
  split (pf_arr) where {
    dataprop EQINT(int,int) = {x:int} EQINT(x,x)
    extern prfun eqint_make{x,y:int | x == y}(): EQINT(x, y)
    extern praxi uncons:
      {a:vtflt}{l:addr}{n:nat}
      arr(a,l,n) -<prf> (a,arr(a,l+sizeof(a),n-1))
    prfun split
      {l:addr} 
      {n,i:nat | i <= n} 
      .<i>.
      (pf_arr: arr (a, l, n)) : (arr (a, l, i), arr(a,l+i*sizeof(a),n-i)) = 
      sif i > 0 then 
        let 
          prval (pfx,pfxs) = uncons(pf_arr)
          prval (pfleft,pfright) = split{l+sizeof(a)}{n-1,i-1}(pfxs)
        in
          (arr_cons (pfx, pfleft), pfright)
        end 
      else 
        let prval EQINT () = eqint_make{i,0}() in (arr_nil{a}{l}((*void*)), pf_arr) end
  } 

fun {a:vtflt} arr_zero
  {n:nat}
  (s:size(n)):[l:addr] arr(a,l,n) = $UN.castvwtp0($extfcall(ptr, "malloc", s*sizeof<a>))

implement main0(argc,argv) = 
  let
  in
    println! "hello world"
  end
  