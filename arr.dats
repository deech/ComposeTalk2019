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

fun {a:tflt} arr_init
  {n:nat}(n:size(n), init:a): [a:vtflt][l:addr] arr(a,l,n) =
  let 
    val p0 = $extfcall(cptr(a),"calloc",n*sizeof<a>,sizeof<a>)
    fun loop(p0:cptr(a),p_end:cptr(a),init:a):void = 
      if (p0 < p_end) then ( 
        $UN.cptr0_set<a>(p0,init); 
        loop(succ(p0), p_end, init) 
      ) 
      else ()
    val () = loop(p0,p0+n*sizeof<a>,init)
  in 
    $UN.castvwtp0(p0)
  end

dataprop EQINT(int,int) = {x:int} EQINT(x,x)
extern prfun eqint_make{x,y:int | x == y}(): EQINT(x, y)
extern praxi uncons{a:vtflt}{l:addr}{n:nat | n > 0}(arr(a,l,n)):(a,arr(a,l+sizeof(a),n-1))
extern praxi unnil{a:vtflt}{l:addr}(arr(a,l,0)):void

prfn arr_unsplit
  {a:vtflt}
  {l:addr}
  {n1,n2:nat}
  (
    pfarr1:arr(a,l,n1), 
    pfarr2:arr(a,l+sizeof(a)*n1,n2)
  ): arr(a,l,n1+n2) =
  unsplit(pfarr1,pfarr2) where {
    prfun unsplit
      {l:addr}{n1,n2:nat}
      .<n1>.
      (pf1:arr(a,l,n1),pf2:arr(a,l+sizeof(a)*n1,n2)):arr(a,l,n1+n2) = 
      sif n1 > 0 then 
        let 
          prval (pfx,pfxs) = uncons(pf1)
          prval pfres      = unsplit(pfxs,pf2)    
        in 
          arr_cons(pfx,pfres)
        end
      else
        let
          prval EQINT () = eqint_make{n1,0}()
          prval () = consume(pf1) where {
            extern praxi consume(arr(a,l,0)):void
          }
        in
          pf2 
        end
  }

prfn arr_split
  {a:vtflt}
  {l:addr}
  {n:int}{i:nat | i <= n}
  (pfarr: arr(a,l,n)): @(arr(a,l,i), arr(a,l+i*sizeof(a),n-i)) =
  split (pfarr) where {
    prfun split
      {l:addr} 
      {n,i:nat | i <= n} 
      .<i>.
      (pfarr: arr (a, l, n)) : (arr (a, l, i), arr(a,l+i*sizeof(a),n-i)) = 
      sif i > 0 then 
        let 
          prval (pfx,pfxs) = uncons(pfarr)
          prval (pfleft,pfright) = split{l+sizeof(a)}{n-1,i-1}(pfxs)
        in
          (arr_cons (pfx, pfleft), pfright)
        end
      else 
        let
          prval EQINT () = eqint_make{i,0}()
        in
         (arr_nil{a}{l}(), pfarr)
        end
  }

fun {a:vtflt} arr_zero
  {n:nat}
  (s:size(n)):[l:addr] arr(a,l,n) = $UN.castvwtp0($extfcall(ptr, "malloc", s*sizeof<a>))

extern fun {a:vtflt} arr_free$inner(a:a): void
extern fun {a:vtflt} arr_free{l:addr}{n:nat}(arr(a,l,n)):void

impltmp{a}arr_free
  (arr):void =
  case+ arr of 
  | ~arr_nil() => ()
  | ~arr_cons(x,xs) => (arr_free$inner(x); arr_free(xs))

implement main0(argc,argv) =
  let 
    val a = arr_cons(string0_copy_vt("a"),
             arr_cons(string0_copy_vt("b"),
               arr_cons(string0_copy_vt("c"),
                 arr_nil())))
    prval (a1,a2) = arr_split{..}{..}{..}{1}(a)
   
  in (
    arr_free<string_vt>(a1) where {
      impltmp arr_free$inner<string_vt>(s) = free s
    };
    arr_free<string_vt>(a2) where {
      impltmp arr_free$inner<string_vt>(s) = free s
    };
  )
  end