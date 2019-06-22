#include "share/HATS/temptory_staload_bucs320.hats"
#staload UN = "libats/SATS/unsafe.sats"
(*
dataviewtype arr(a:vtflt, addr, int) = 
  | {l:addr}
    arr_nil(a,l,0) of ()
  | {l:addr}{n:nat}
    arr_cons(a,l,n+1) of (a@l,arr(a,l+sizeof(a),n))

*)

dataviewtype arr(a:vtflt,addr,int) = 
 | {l:addr}
   arr_nil(a,l,0) of ()
 | {l:addr}{n:nat}
   arr_cons(a,l,n+1) of (a,arr(a,l+sizeof(a),n)) 

fun {a:vtflt} arr_zero
  {n:nat}
  (s:size(n)):[l:addr] arr(a,l,n) = $UN.castvwtp0($extfcall(cptr0(a), "malloc", s*sizeof<a>))

fun {a:vtflt} arr_init
  {n:nat}
  (s:size(n), n:int(n), a:a): [l:addr] arr(a,l,n) = 

fun {a:vtflt} test
  {n:nat}(s:size(n)): [l:addr] arr(a?,l,n) = arr_zero(s)

implement main0(argc,argv) = 
  let
  in
    println! "hello world"
  end
  