%{
  #include <string.h>
%}
#include "share/HATS/temptory_staload_bucs320.hats"
#staload UN = "libats/SATS/unsafe.sats"

datavtype FileHandle = FileHandle of ()
    
fun fopen(path:string,mode:string): FileHandle =
  let
    extern castfn toFileHandle(p:ptr0):<> FileHandle
  in
    toFileHandle($extfcall(ptr0,"fopen",path,mode))
  end

fun fclose(f:FileHandle):void =
  let 
    extern castfn fromFH(f:FileHandle):<> ptr0
  in
    $extfcall(void,"fclose", fromFH(f))
  end

fun fwithline(
    fh: !FileHandle,
    f: &(string) -<clo1> void
    ):void =
  let
    var len = i2sz(0)
    val lenP = addr@len
    var buffer = the_null_ptr
    val bufferP = addr@buffer
    extern castfn toPtr{l:addr}(f: !FileHandle):<> ptr0
    val _ = $extfcall(int,"getline",bufferP,lenP,toPtr(fh))
  in
    f ($UN.castvwtp0{string}(buffer))
  end

implement main0(argc,argv) =
  let
    val a = fopen("test.txt","r")
    val b = fopen("test.txt","r")
    var f = lam@(s:string):void => println! s
  in (
    fwithline(a,f);
    fclose(a);
    fclose(b)
  )
  end