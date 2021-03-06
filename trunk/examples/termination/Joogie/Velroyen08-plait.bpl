type ref;
type realVar;
type classConst;
// type Field x;
// var $HeapVar : <x>[ref, Field x]x;

const unique $null : ref ;
const unique $intArrNull : [int]int ;
const unique $realArrNull : [int]realVar ;
const unique $refArrNull : [int]ref ;

const unique $arrSizeIdx : int;
var $intArrSize : [int]int;
var $realArrSize : [realVar]int;
var $refArrSize : [ref]int;

var $stringSize : [ref]int;

//built-in axioms 
axiom ($arrSizeIdx == -1);

//note: new version doesn't put helpers in the perlude anymore//Prelude finished 





// procedure is generated by joogie.
function {:inline true} $neref(x : ref, y : ref) returns (__ret : int) {
if (x != y) then 1 else 0
}


// procedure is generated by joogie.
function {:inline true} $realarrtoref($param00 : [int]realVar) returns (__ret : ref);



// procedure is generated by joogie.
function {:inline true} $modreal($param00 : realVar, $param11 : realVar) returns (__ret : realVar);



// procedure is generated by joogie.
function {:inline true} $leref($param00 : ref, $param11 : ref) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $modint($param00 : int, $param11 : int) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $gtref($param00 : ref, $param11 : ref) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $eqrealarray($param00 : [int]realVar, $param11 : [int]realVar) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $addint(x : int, y : int) returns (__ret : int) {
(x + y)
}


// procedure is generated by joogie.
function {:inline true} $subref($param00 : ref, $param11 : ref) returns (__ret : ref);



// procedure is generated by joogie.
function {:inline true} $inttoreal($param00 : int) returns (__ret : realVar);



// procedure is generated by joogie.
function {:inline true} $shrint($param00 : int, $param11 : int) returns (__ret : int);



	 //  @line: 7
// <simple.plait.Plait: void loop(int,int,int)>
procedure void$simple.plait.Plait$loop$2231($param_0 : int, $param_1 : int, $param_2 : int) {
var i116 : int;
var z018 : int;
var i217 : int;
var i421 : int;
var i320 : int;
var i015 : int;
Block19:
	i015 := $param_0;
	i116 := $param_1;
	i217 := $param_2;
	 //  @line: 8
	z018 := 0;
	 goto Block20;
	 //  @line: 10
Block20:
	 goto Block21, Block23;
	 //  @line: 10
Block21:
	 assume ($gtint((i015), (0))==1);
	 goto Block22;
	 //  @line: 10
Block23:
	 //  @line: 10
	 assume ($negInt(($gtint((i015), (0))))==1);
	 goto Block24;
	 //  @line: 11
Block22:
	 goto Block31, Block33;
	 //  @line: 10
Block24:
	 goto Block26, Block25;
	 //  @line: 11
Block31:
	 assume ($neint((z018), (0))==1);
	 goto Block32;
	 //  @line: 11
Block33:
	 //  @line: 11
	 assume ($negInt(($neint((z018), (0))))==1);
	 //  @line: 12
	i320 := i015;
	 assert ($neint((2), (0))==1);
	 //  @line: 13
	i015 := $divint((i116), (2));
	 //  @line: 14
	i116 := $mulint((i320), (2));
	 //  @line: 15
	z018 := 1;
	 goto Block20;
	 //  @line: 10
Block26:
	 //  @line: 10
	 assume ($negInt(($gtint((i116), (0))))==1);
	 goto Block27;
	 //  @line: 10
Block25:
	 assume ($gtint((i116), (0))==1);
	 goto Block22;
	 //  @line: 17
Block32:
	 //  @line: 17
	i421 := i217;
	 goto Block34;
	 //  @line: 11
Block27:
	 goto Block28, Block30;
	 //  @line: 18
Block34:
	 //  @line: 18
	i217 := $mulint((i116), (2));
	 assert ($neint((2), (0))==1);
	 //  @line: 19
	i116 := $divint((i421), (2));
	 //  @line: 20
	z018 := 0;
	 goto Block20;
	 //  @line: 11
Block28:
	 assume ($leint((i217), (0))==1);
	 goto Block29;
	 //  @line: 11
Block30:
	 //  @line: 11
	 assume ($negInt(($leint((i217), (0))))==1);
	 goto Block22;
	 //  @line: 24
Block29:
	 return;
}


// procedure is generated by joogie.
function {:inline true} $negReal($param00 : realVar) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $ushrint($param00 : int, $param11 : int) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $refarrtoref($param00 : [int]ref) returns (__ret : ref);



// procedure is generated by joogie.
function {:inline true} $divref($param00 : ref, $param11 : ref) returns (__ret : ref);



// procedure is generated by joogie.
function {:inline true} $mulref($param00 : ref, $param11 : ref) returns (__ret : ref);



// procedure is generated by joogie.
function {:inline true} $neint(x : int, y : int) returns (__ret : int) {
if (x != y) then 1 else 0
}


// procedure is generated by joogie.
function {:inline true} $ltreal($param00 : realVar, $param11 : realVar) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $reftorefarr($param00 : ref) returns (__ret : [int]ref);



// procedure is generated by joogie.
function {:inline true} $gtint(x : int, y : int) returns (__ret : int) {
if (x > y) then 1 else 0
}


// procedure is generated by joogie.
function {:inline true} $reftoint($param00 : ref) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $addref($param00 : ref, $param11 : ref) returns (__ret : ref);



// <java.lang.Object: void <init>()>
procedure void$java.lang.Object$$la$init$ra$$28(__this : ref);



// procedure is generated by joogie.
function {:inline true} $xorreal($param00 : realVar, $param11 : realVar) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $andref($param00 : ref, $param11 : ref) returns (__ret : int);



	 //  @line: 8
// <simple.plait.Main: void main(java.lang.String[])>
procedure void$simple.plait.Main$main$2229($param_0 : [int]ref)
  modifies $stringSize;
 {
var $r25 : ref;
var $r37 : ref;
var $r13 : ref;
var $i04 : int;
var r02 : [int]ref;
var $i16 : int;
var $i28 : int;
Block17:
	r02 := $param_0;
	 assert ($geint((0), (0))==1);
	 assert ($ltint((0), ($refArrSize[r02[$arrSizeIdx]]))==1);
	 //  @line: 9
	$r13 := r02[0];
	$i04 := $stringSize[$r13];
	 assert ($geint((1), (0))==1);
	 assert ($ltint((1), ($refArrSize[r02[$arrSizeIdx]]))==1);
	 //  @line: 9
	$r25 := r02[1];
	$i16 := $stringSize[$r25];
	 assert ($geint((2), (0))==1);
	 assert ($ltint((2), ($refArrSize[r02[$arrSizeIdx]]))==1);
	 //  @line: 9
	$r37 := r02[2];
	$i28 := $stringSize[$r37];
	 //  @line: 9
	 call void$simple.plait.Plait$loop$2231(($i04), ($i16), ($i28));
	 return;
}


// procedure is generated by joogie.
function {:inline true} $cmpreal(x : realVar, y : realVar) returns (__ret : int) {
if ($ltreal((x), (y)) == 1) then 1 else if ($eqreal((x), (y)) == 1) then 0 else -1
}


// procedure is generated by joogie.
function {:inline true} $addreal($param00 : realVar, $param11 : realVar) returns (__ret : realVar);



// procedure is generated by joogie.
function {:inline true} $gtreal($param00 : realVar, $param11 : realVar) returns (__ret : int);



	 //  @line: 2
// <simple.plait.Plait: void <init>()>
procedure void$simple.plait.Plait$$la$init$ra$$2230(__this : ref)  requires ($neref((__this), ($null))==1);
 {
var r09 : ref;
Block18:
	r09 := __this;
	 assert ($neref((r09), ($null))==1);
	 //  @line: 3
	 call void$java.lang.Object$$la$init$ra$$28((r09));
	 return;
}


// procedure is generated by joogie.
function {:inline true} $eqreal(x : realVar, y : realVar) returns (__ret : int) {
if (x == y) then 1 else 0
}


// procedure is generated by joogie.
function {:inline true} $ltint(x : int, y : int) returns (__ret : int) {
if (x < y) then 1 else 0
}


// procedure is generated by joogie.
function {:inline true} $newvariable($param00 : int) returns (__ret : ref);



// procedure is generated by joogie.
function {:inline true} $divint($param00 : int, $param11 : int) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $geint(x : int, y : int) returns (__ret : int) {
if (x >= y) then 1 else 0
}


// procedure is generated by joogie.
function {:inline true} $mulint($param00 : int, $param11 : int) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $leint(x : int, y : int) returns (__ret : int) {
if (x <= y) then 1 else 0
}


// procedure is generated by joogie.
function {:inline true} $shlref($param00 : ref, $param11 : ref) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $eqrefarray($param00 : [int]ref, $param11 : [int]ref) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $reftointarr($param00 : ref) returns (__ret : [int]int);



// procedure is generated by joogie.
function {:inline true} $ltref($param00 : ref, $param11 : ref) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $mulreal($param00 : realVar, $param11 : realVar) returns (__ret : realVar);



// procedure is generated by joogie.
function {:inline true} $shrref($param00 : ref, $param11 : ref) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $ushrreal($param00 : realVar, $param11 : realVar) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $shrreal($param00 : realVar, $param11 : realVar) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $divreal($param00 : realVar, $param11 : realVar) returns (__ret : realVar);



// procedure is generated by joogie.
function {:inline true} $orint($param00 : int, $param11 : int) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $reftorealarr($param00 : ref) returns (__ret : [int]realVar);



// procedure is generated by joogie.
function {:inline true} $cmpref(x : ref, y : ref) returns (__ret : int) {
if ($ltref((x), (y)) == 1) then 1 else if ($eqref((x), (y)) == 1) then 0 else -1
}


// procedure is generated by joogie.
function {:inline true} $realtoint($param00 : realVar) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $geref($param00 : ref, $param11 : ref) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $orreal($param00 : realVar, $param11 : realVar) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $eqint(x : int, y : int) returns (__ret : int) {
if (x == y) then 1 else 0
}


// procedure is generated by joogie.
function {:inline true} $ushrref($param00 : ref, $param11 : ref) returns (__ret : int);



// <java.lang.String: int length()>
procedure int$java.lang.String$length$59(__this : ref) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $modref($param00 : ref, $param11 : ref) returns (__ret : ref);



// procedure is generated by joogie.
function {:inline true} $eqintarray($param00 : [int]int, $param11 : [int]int) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $negRef($param00 : ref) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $lereal($param00 : realVar, $param11 : realVar) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $nereal(x : realVar, y : realVar) returns (__ret : int) {
if (x != y) then 1 else 0
}


// procedure is generated by joogie.
function {:inline true} $instanceof($param00 : ref, $param11 : classConst) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $xorref($param00 : ref, $param11 : ref) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $orref($param00 : ref, $param11 : ref) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $intarrtoref($param00 : [int]int) returns (__ret : ref);



// procedure is generated by joogie.
function {:inline true} $subreal($param00 : realVar, $param11 : realVar) returns (__ret : realVar);



// procedure is generated by joogie.
function {:inline true} $shlreal($param00 : realVar, $param11 : realVar) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $negInt(x : int) returns (__ret : int) {
if (x == 0) then 1 else 0
}


// procedure is generated by joogie.
function {:inline true} $gereal($param00 : realVar, $param11 : realVar) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $eqref(x : ref, y : ref) returns (__ret : int) {
if (x == y) then 1 else 0
}


	 //  @line: 2
// <simple.plait.Main: void <init>()>
procedure void$simple.plait.Main$$la$init$ra$$2228(__this : ref)  requires ($neref((__this), ($null))==1);
 {
var r01 : ref;
Block16:
	r01 := __this;
	 assert ($neref((r01), ($null))==1);
	 //  @line: 3
	 call void$java.lang.Object$$la$init$ra$$28((r01));
	 return;
}


// procedure is generated by joogie.
function {:inline true} $cmpint(x : int, y : int) returns (__ret : int) {
if (x < y) then 1 else if (x == y) then 0 else -1
}


// procedure is generated by joogie.
function {:inline true} $andint($param00 : int, $param11 : int) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $andreal($param00 : realVar, $param11 : realVar) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $shlint($param00 : int, $param11 : int) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $xorint($param00 : int, $param11 : int) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $subint(x : int, y : int) returns (__ret : int) {
(x - y)
}


