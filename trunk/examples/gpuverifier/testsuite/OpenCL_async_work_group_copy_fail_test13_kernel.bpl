//#Unsafe
type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP32(x: [bv32]bv32, y: bv32) returns (z$1: bv32, A$1: [bv32]bv32, z$2: bv32, A$2: [bv32]bv32);

axiom {:array_info "$$p"} {:global} {:elem_width 32} {:source_name "p"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$p: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$p: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$p: bool;

var {:source_name "q"} {:global} $$q: [bv32]bv32;

axiom {:array_info "$$q"} {:global} {:elem_width 32} {:source_name "q"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$q: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$q: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$q: bool;

axiom {:array_info "$$handle"} {:elem_width 32} {:source_name "handle"} {:source_elem_width 32} {:source_dimensions "1"} true;

var {:source_name "mydata"} {:group_shared} $$foo.mydata: [bv1][bv32]bv32;

axiom {:array_info "$$foo.mydata"} {:group_shared} {:elem_width 32} {:source_name "mydata"} {:source_elem_width 32} {:source_dimensions "1024"} true;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$foo.mydata: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$foo.mydata: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$foo.mydata: bool;

const _WATCHED_OFFSET: bv32;

const {:global_offset_x} global_offset_x: bv32;

const {:global_offset_y} global_offset_y: bv32;

const {:global_offset_z} global_offset_z: bv32;

const {:group_id_x} group_id_x$1: bv32;

const {:group_id_x} group_id_x$2: bv32;

const {:group_size_x} group_size_x: bv32;

const {:group_size_y} group_size_y: bv32;

const {:group_size_z} group_size_z: bv32;

const {:local_id_x} local_id_x$1: bv32;

const {:local_id_x} local_id_x$2: bv32;

const {:num_groups_x} num_groups_x: bv32;

const {:num_groups_y} num_groups_y: bv32;

const {:num_groups_z} num_groups_z: bv32;

function {:builtin "bvadd"} BV32_ADD(bv32, bv32) : bv32;

function {:builtin "bvmul"} BV32_MUL(bv32, bv32) : bv32;

procedure {:async_work_group_copy} _ASYNC_WORK_GROUP_COPY_32(dstOffset: bv32, srcOffset: bv32, size: bv32, handle: bv32, src$1: [bv32]bv32, src$2: [bv32]bv32) returns (handle'$1: bv32, dst$1: [bv32]bv32, handle'$2: bv32, dst$2: [bv32]bv32);
  requires dstOffset == 0bv32;
  requires srcOffset == 0bv32;
  requires size == 1024bv32;
  requires handle == 0bv32;

procedure {:wait_group_events} _WAIT_GROUP_EVENTS(handle$1: bv32, handle$2: bv32);

procedure {:source_name "foo"} ULTIMATE.start();
  requires !_READ_HAS_OCCURRED_$$p && !_WRITE_HAS_OCCURRED_$$p && !_ATOMIC_HAS_OCCURRED_$$p;
  requires !_READ_HAS_OCCURRED_$$q && !_WRITE_HAS_OCCURRED_$$q && !_ATOMIC_HAS_OCCURRED_$$q;
  requires !_READ_HAS_OCCURRED_$$foo.mydata && !_WRITE_HAS_OCCURRED_$$foo.mydata && !_ATOMIC_HAS_OCCURRED_$$foo.mydata;
  requires BV32_SGT(group_size_x, 0bv32);
  requires BV32_SGT(num_groups_x, 0bv32);
  requires BV32_SGE(group_id_x$1, 0bv32);
  requires BV32_SGE(group_id_x$2, 0bv32);
  requires BV32_SLT(group_id_x$1, num_groups_x);
  requires BV32_SLT(group_id_x$2, num_groups_x);
  requires BV32_SGE(local_id_x$1, 0bv32);
  requires BV32_SGE(local_id_x$2, 0bv32);
  requires BV32_SLT(local_id_x$1, group_size_x);
  requires BV32_SLT(local_id_x$2, group_size_x);
  requires BV32_SGT(group_size_y, 0bv32);
  requires BV32_SGT(num_groups_y, 0bv32);
  requires BV32_SGE(group_id_y$1, 0bv32);
  requires BV32_SGE(group_id_y$2, 0bv32);
  requires BV32_SLT(group_id_y$1, num_groups_y);
  requires BV32_SLT(group_id_y$2, num_groups_y);
  requires BV32_SGE(local_id_y$1, 0bv32);
  requires BV32_SGE(local_id_y$2, 0bv32);
  requires BV32_SLT(local_id_y$1, group_size_y);
  requires BV32_SLT(local_id_y$2, group_size_y);
  requires BV32_SGT(group_size_z, 0bv32);
  requires BV32_SGT(num_groups_z, 0bv32);
  requires BV32_SGE(group_id_z$1, 0bv32);
  requires BV32_SGE(group_id_z$2, 0bv32);
  requires BV32_SLT(group_id_z$1, num_groups_z);
  requires BV32_SLT(group_id_z$2, num_groups_z);
  requires BV32_SGE(local_id_z$1, 0bv32);
  requires BV32_SGE(local_id_z$2, 0bv32);
  requires BV32_SLT(local_id_z$1, group_size_z);
  requires BV32_SLT(local_id_z$2, group_size_z);
  requires group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> local_id_x$1 != local_id_x$2 || local_id_y$1 != local_id_y$2 || local_id_z$1 != local_id_z$2;
  modifies _READ_ASYNC_HANDLE_$$p, _WRITE_ASYNC_HANDLE_$$foo.mydata, $$foo.mydata, $$q, _TRACKING, _READ_HAS_OCCURRED_$$foo.mydata, _WRITE_HAS_OCCURRED_$$q, _WRITE_READ_BENIGN_FLAG_$$q, _WRITE_READ_BENIGN_FLAG_$$q, _WRITE_HAS_OCCURRED_$$foo.mydata, _WRITE_READ_BENIGN_FLAG_$$foo.mydata, _WRITE_ASYNC_HANDLE_$$foo.mydata, _READ_HAS_OCCURRED_$$p, _READ_ASYNC_HANDLE_$$p;

implementation {:source_name "foo"} ULTIMATE.start()
{
  var v0$1: bv32;
  var v0$2: bv32;
  var v2$1: bv32;
  var v2$2: bv32;
  var v1$1: bv32;
  var v1$2: bv32;

  __partitioned_block_$entry_0:
    call v0$1, v0$2 := _ASYNC_WORK_GROUP_COPY_$$foo.mydata_$$p(true, 0bv32, 0bv32, 1024bv32, 0bv32, true, 0bv32, 0bv32, 1024bv32, 0bv32);
    $$handle$0bv32$1 := v0$1;
    $$handle$0bv32$2 := v0$2;
    goto __partitioned_block_$entry_1;

  __partitioned_block_$entry_1:
    call $bugle_barrier_duplicated_0(1bv1, 1bv1);
    call _LOG_READ_$$foo.mydata(true, BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), $$foo.mydata[1bv1][BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)]);
    assume {:do_not_predicate} {:check_id "check_state_2"} {:captureState "check_state_2"} {:sourceloc} {:sourceloc_num 4} true;
    call _CHECK_READ_$$foo.mydata(true, BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), $$foo.mydata[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$foo.mydata"} true;
    v1$1 := $$foo.mydata[1bv1][BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)];
    v1$2 := $$foo.mydata[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)];
    call _LOG_WRITE_$$q(true, BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), v1$1, $$q[BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$q(true, BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2));
    assume {:do_not_predicate} {:check_id "check_state_3"} {:captureState "check_state_3"} {:sourceloc} {:sourceloc_num 5} true;
    call _CHECK_WRITE_$$q(true, BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), v1$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$q"} true;
    $$q[BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)] := v1$1;
    $$q[BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)] := v1$2;
    v2$1 := $$handle$0bv32$1;
    v2$2 := $$handle$0bv32$2;
    assert {:sourceloc_num 7} {:thread 1} group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> true == true;
    assert {:sourceloc_num 7} {:thread 1} group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> v2$1 == v2$2;
    assert {:sourceloc_num 7} {:thread 2} group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> v2$2 == v2$1;
    _READ_ASYNC_HANDLE_$$p := (if v2$1 == _READ_ASYNC_HANDLE_$$p then _ASYNC_NO_HANDLE else _READ_ASYNC_HANDLE_$$p);
    _READ_ASYNC_HANDLE_$$p := (if v2$2 == _READ_ASYNC_HANDLE_$$p then _ASYNC_NO_HANDLE else _READ_ASYNC_HANDLE_$$p);
    _WRITE_ASYNC_HANDLE_$$foo.mydata := (if v2$1 == _WRITE_ASYNC_HANDLE_$$foo.mydata then _ASYNC_NO_HANDLE else _WRITE_ASYNC_HANDLE_$$foo.mydata);
    _WRITE_ASYNC_HANDLE_$$foo.mydata := (if v2$2 == _WRITE_ASYNC_HANDLE_$$foo.mydata then _ASYNC_NO_HANDLE else _WRITE_ASYNC_HANDLE_$$foo.mydata);
    return;
}

axiom (if group_size_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_x == 1024bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_x == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if global_offset_x == 0bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if global_offset_y == 0bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if global_offset_z == 0bv32 then 1bv1 else 0bv1) != 0bv1;

const {:local_id_y} local_id_y$1: bv32;

const {:local_id_y} local_id_y$2: bv32;

const {:local_id_z} local_id_z$1: bv32;

const {:local_id_z} local_id_z$2: bv32;

const {:group_id_y} group_id_y$1: bv32;

const {:group_id_y} group_id_y$2: bv32;

const {:group_id_z} group_id_z$1: bv32;

const {:group_id_z} group_id_z$2: bv32;

procedure {:inline 1} {:safe_barrier} {:source_name "bugle_barrier"} {:barrier} $bugle_barrier_duplicated_0($0: bv1, $1: bv1);
  requires $0 == 1bv1;
  requires $1 == 1bv1;
  modifies $$foo.mydata, $$q, _TRACKING;

var $$handle$0bv32$1: bv32;

var $$handle$0bv32$2: bv32;

const _ASYNC_NO_HANDLE: bv32;

axiom _ASYNC_NO_HANDLE == 0bv32;

function {:builtin "bvuge"} BV32_UGE(bv32, bv32) : bool;

function {:builtin "bvult"} BV32_ULT(bv32, bv32) : bool;

procedure {:inline 1} _ASYNC_WORK_GROUP_COPY_$$foo.mydata_$$p(_P$1: bool, DstOffset$1: bv32, SrcOffset$1: bv32, Size$1: bv32, Handle$1: bv32, _P$2: bool, DstOffset$2: bv32, SrcOffset$2: bv32, Size$2: bv32, Handle$2: bv32) returns (ResultHandle$1: bv32, ResultHandle$2: bv32);
  requires _P$1 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> _P$1 == _P$2;
  requires _P$2 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> _P$2 == _P$1;
  requires _P$1 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> DstOffset$1 == DstOffset$2;
  requires _P$2 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> DstOffset$2 == DstOffset$1;
  requires _P$1 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> SrcOffset$1 == SrcOffset$2;
  requires _P$2 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> SrcOffset$2 == SrcOffset$1;
  requires _P$1 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> Size$1 == Size$2;
  requires _P$2 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> Size$2 == Size$1;
  requires _P$1 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> Handle$1 == Handle$2;
  requires _P$2 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> Handle$2 == Handle$1;
  modifies _WRITE_HAS_OCCURRED_$$foo.mydata, _WRITE_READ_BENIGN_FLAG_$$foo.mydata, _WRITE_ASYNC_HANDLE_$$foo.mydata, _READ_HAS_OCCURRED_$$p, _READ_ASYNC_HANDLE_$$p;

implementation {:inline 1} _ASYNC_WORK_GROUP_COPY_$$foo.mydata_$$p(_P$1: bool, DstOffset$1: bv32, SrcOffset$1: bv32, Size$1: bv32, Handle$1: bv32, _P$2: bool, DstOffset$2: bv32, SrcOffset$2: bv32, Size$2: bv32, Handle$2: bv32) returns (ResultHandle$1: bv32, ResultHandle$2: bv32)
{
  var Index$1: bv32;
  var Index$2: bv32;
  var IdX$1: bv32;
  var IdX$2: bv32;
  var IdY$1: bv32;
  var IdY$2: bv32;
  var IdZ$1: bv32;
  var IdZ$2: bv32;
  var _abstracted_call_arg_0$1: bv32;
  var _abstracted_call_arg_0$2: bv32;
  var _abstracted_call_arg_1$1: bv32;
  var _abstracted_call_arg_1$2: bv32;
  var _abstracted_call_arg_2$1: bv32;
  var _abstracted_call_arg_2$2: bv32;
  var _abstracted_call_arg_3$1: bv32;
  var _abstracted_call_arg_3$2: bv32;
  var p0$1: bool;
  var p0$2: bool;
  var p1$1: bool;
  var p1$2: bool;
  var _HAVOC_bv32$1: bv32;
  var _HAVOC_bv32$2: bv32;

  entry:
    assume (_P$1 ==> ResultHandle$1 != _ASYNC_NO_HANDLE) && (_P$2 ==> ResultHandle$2 != _ASYNC_NO_HANDLE);
    ResultHandle$1 := (if _P$1 then (if Handle$1 == _ASYNC_NO_HANDLE then ResultHandle$1 else Handle$1) else ResultHandle$1);
    ResultHandle$2 := (if _P$2 then (if Handle$2 == _ASYNC_NO_HANDLE then ResultHandle$2 else Handle$2) else ResultHandle$2);
    assume (_P$1 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> ResultHandle$1 == ResultHandle$2) && (_P$2 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> ResultHandle$2 == ResultHandle$1);
    assume (_P$1 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> IdX$1 == IdX$2) && (_P$2 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> IdX$2 == IdX$1);
    assume (_P$1 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> IdY$1 == IdY$2) && (_P$2 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> IdY$2 == IdY$1);
    assume (_P$1 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> IdZ$1 == IdZ$2) && (_P$2 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> IdZ$2 == IdZ$1);
    p0$1 := false;
    p0$2 := false;
    p1$1 := false;
    p1$2 := false;
    p0$1 := (if _P$1 && IdX$1 == local_id_x$1 && IdY$1 == local_id_y$1 && IdZ$1 == local_id_z$1 then IdX$1 == local_id_x$1 && IdY$1 == local_id_y$1 && IdZ$1 == local_id_z$1 else p0$1);
    p0$2 := (if _P$2 && IdX$2 == local_id_x$2 && IdY$2 == local_id_y$2 && IdZ$2 == local_id_z$2 then IdX$2 == local_id_x$2 && IdY$2 == local_id_y$2 && IdZ$2 == local_id_z$2 else p0$2);
    assume (p0$1 ==> BV32_UGE(Index$1, 0bv32)) && (p0$2 ==> BV32_UGE(Index$2, 0bv32));
    assume (p0$1 ==> BV32_ULT(Index$1, Size$1)) && (p0$2 ==> BV32_ULT(Index$2, Size$2));
    havoc _HAVOC_bv32$1, _HAVOC_bv32$2;
    _abstracted_call_arg_0$1 := (if p0$1 then _HAVOC_bv32$1 else _abstracted_call_arg_0$1);
    _abstracted_call_arg_0$2 := (if p0$2 then _HAVOC_bv32$2 else _abstracted_call_arg_0$2);
    call _LOG_WRITE_$$foo.mydata(p0$1, BV32_ADD(DstOffset$1, Index$1), _abstracted_call_arg_0$1, $$foo.mydata[1bv1][BV32_ADD(DstOffset$1, Index$1)], ResultHandle$1);
    assume {:do_not_predicate} {:check_id "check_state_0"} {:captureState "check_state_0"} {:sourceloc} {:sourceloc_num 1} true;
    havoc _HAVOC_bv32$1, _HAVOC_bv32$2;
    _abstracted_call_arg_1$1 := (if p0$1 then _HAVOC_bv32$1 else _abstracted_call_arg_1$1);
    _abstracted_call_arg_1$2 := (if p0$2 then _HAVOC_bv32$2 else _abstracted_call_arg_1$2);
    call _CHECK_WRITE_$$foo.mydata(p0$2, BV32_ADD(DstOffset$2, Index$2), _abstracted_call_arg_1$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$foo.mydata"} true;
    havoc _HAVOC_bv32$1, _HAVOC_bv32$2;
    _abstracted_call_arg_2$1 := (if p0$1 then _HAVOC_bv32$1 else _abstracted_call_arg_2$1);
    _abstracted_call_arg_2$2 := (if p0$2 then _HAVOC_bv32$2 else _abstracted_call_arg_2$2);
    call _LOG_READ_$$p(p0$1, BV32_ADD(SrcOffset$1, Index$1), _abstracted_call_arg_2$1, ResultHandle$1);
    assume {:do_not_predicate} {:check_id "check_state_1"} {:captureState "check_state_1"} {:sourceloc} {:sourceloc_num 1} true;
    havoc _HAVOC_bv32$1, _HAVOC_bv32$2;
    _abstracted_call_arg_3$1 := (if p0$1 then _HAVOC_bv32$1 else _abstracted_call_arg_3$1);
    _abstracted_call_arg_3$2 := (if p0$2 then _HAVOC_bv32$2 else _abstracted_call_arg_3$2);
    call _CHECK_READ_$$p(p0$2, BV32_ADD(SrcOffset$2, Index$2), _abstracted_call_arg_3$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$p"} true;
    return;
}

const _WATCHED_VALUE_$$p: bv32;

var _READ_ASYNC_HANDLE_$$p: bv32;

procedure {:inline 1} _LOG_READ_$$p(_P: bool, _offset: bv32, _value: bv32, _async_handle: bv32);
  modifies _READ_HAS_OCCURRED_$$p, _READ_ASYNC_HANDLE_$$p;

implementation {:inline 1} _LOG_READ_$$p(_P: bool, _offset: bv32, _value: bv32, _async_handle: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$p := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p == _value then true else _READ_HAS_OCCURRED_$$p);
    _READ_ASYNC_HANDLE_$$p := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p == _value then _async_handle else _READ_ASYNC_HANDLE_$$p);
    return;
}

procedure _CHECK_READ_$$p(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$p && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$p);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$p && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$p: bool;

procedure {:inline 1} _LOG_WRITE_$$p(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$p, _WRITE_READ_BENIGN_FLAG_$$p;

implementation {:inline 1} _LOG_WRITE_$$p(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$p := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p == _value then true else _WRITE_HAS_OCCURRED_$$p);
    _WRITE_READ_BENIGN_FLAG_$$p := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$p);
    return;
}

procedure _CHECK_WRITE_$$p(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$p && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$p && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$p && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$p(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$p;

implementation {:inline 1} _LOG_ATOMIC_$$p(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$p := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$p);
    return;
}

procedure _CHECK_ATOMIC_$$p(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$p && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$p && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$p(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$p;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$p(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$p := (if _P && _WRITE_HAS_OCCURRED_$$p && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$p);
    return;
}

const _WATCHED_VALUE_$$q: bv32;

procedure {:inline 1} _LOG_READ_$$q(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$q;

implementation {:inline 1} _LOG_READ_$$q(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$q := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$q == _value then true else _READ_HAS_OCCURRED_$$q);
    return;
}

procedure _CHECK_READ_$$q(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$q && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$q);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$q && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$q: bool;

procedure {:inline 1} _LOG_WRITE_$$q(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$q, _WRITE_READ_BENIGN_FLAG_$$q;

implementation {:inline 1} _LOG_WRITE_$$q(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$q := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$q == _value then true else _WRITE_HAS_OCCURRED_$$q);
    _WRITE_READ_BENIGN_FLAG_$$q := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$q == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$q);
    return;
}

procedure _CHECK_WRITE_$$q(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$q && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$q != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$q && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$q != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$q && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$q(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$q;

implementation {:inline 1} _LOG_ATOMIC_$$q(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$q := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$q);
    return;
}

procedure _CHECK_ATOMIC_$$q(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$q && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$q && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$q(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$q;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$q(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$q := (if _P && _WRITE_HAS_OCCURRED_$$q && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$q);
    return;
}

const _WATCHED_VALUE_$$foo.mydata: bv32;

procedure {:inline 1} _LOG_READ_$$foo.mydata(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$foo.mydata;

implementation {:inline 1} _LOG_READ_$$foo.mydata(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$foo.mydata := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.mydata == _value then true else _READ_HAS_OCCURRED_$$foo.mydata);
    return;
}

procedure _CHECK_READ_$$foo.mydata(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.mydata && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$foo.mydata && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$foo.mydata && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

var _WRITE_READ_BENIGN_FLAG_$$foo.mydata: bool;

var _WRITE_ASYNC_HANDLE_$$foo.mydata: bv32;

procedure {:inline 1} _LOG_WRITE_$$foo.mydata(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32, _async_handle: bv32);
  modifies _WRITE_HAS_OCCURRED_$$foo.mydata, _WRITE_READ_BENIGN_FLAG_$$foo.mydata, _WRITE_ASYNC_HANDLE_$$foo.mydata;

implementation {:inline 1} _LOG_WRITE_$$foo.mydata(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32, _async_handle: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$foo.mydata := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.mydata == _value then true else _WRITE_HAS_OCCURRED_$$foo.mydata);
    _WRITE_READ_BENIGN_FLAG_$$foo.mydata := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.mydata == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$foo.mydata);
    _WRITE_ASYNC_HANDLE_$$foo.mydata := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.mydata == _value then _async_handle else _WRITE_ASYNC_HANDLE_$$foo.mydata);
    return;
}

procedure _CHECK_WRITE_$$foo.mydata(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.mydata && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.mydata != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$foo.mydata && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.mydata != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$foo.mydata && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _LOG_ATOMIC_$$foo.mydata(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$foo.mydata;

implementation {:inline 1} _LOG_ATOMIC_$$foo.mydata(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$foo.mydata := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$foo.mydata);
    return;
}

procedure _CHECK_ATOMIC_$$foo.mydata(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.mydata && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$foo.mydata && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$foo.mydata(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$foo.mydata;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$foo.mydata(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$foo.mydata := (if _P && _WRITE_HAS_OCCURRED_$$foo.mydata && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$foo.mydata);
    return;
}

var _TRACKING: bool;

implementation {:inline 1} $bugle_barrier_duplicated_0($0: bv1, $1: bv1)
{

  __BarrierImpl:
    goto anon7_Then, anon7_Else;

  anon7_Else:
    assume {:partition} true;
    goto anon0;

  anon0:
    assume $0 != 0bv1 ==> !_READ_HAS_OCCURRED_$$foo.mydata;
    assume _WRITE_ASYNC_HANDLE_$$foo.mydata == _ASYNC_NO_HANDLE ==> $0 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$foo.mydata;
    assume $0 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$foo.mydata;
    goto anon1;

  anon1:
    goto anon8_Then, anon8_Else;

  anon8_Else:
    assume {:partition} !($0 != 0bv1 || $0 != 0bv1);
    goto anon3;

  anon3:
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_READ_HAS_OCCURRED_$$q;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$q;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$q;
    goto anon4;

  anon4:
    goto anon9_Then, anon9_Else;

  anon9_Else:
    assume {:partition} !(group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && ($1 != 0bv1 || $1 != 0bv1));
    goto anon6;

  anon6:
    havoc _TRACKING;
    return;

  anon9_Then:
    assume {:partition} group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && ($1 != 0bv1 || $1 != 0bv1);
    havoc $$q;
    goto anon6;

  anon8_Then:
    assume {:partition} $0 != 0bv1 || $0 != 0bv1;
    havoc $$foo.mydata;
    goto anon3;

  anon7_Then:
    assume {:partition} false;
    goto __Disabled;

  __Disabled:
    return;
}

function {:builtin "bvsgt"} BV32_SGT(bv32, bv32) : bool;

function {:builtin "bvsge"} BV32_SGE(bv32, bv32) : bool;

function {:builtin "bvslt"} BV32_SLT(bv32, bv32) : bool;
