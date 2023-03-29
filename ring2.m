const
  N: 12;  -- 环上的节点数

type
  NODE : 1..N;
  NUM : 0..N;
  MSG_STATE: enum {IDLE, ELECTION, LEADER}; -- 消息状态
  Node_STATE : enum {valid, invalid}; -- 节点状态

  MSG : record
    MSG_TYPE: MSG_STATE;
    MSG_Leader : NODE;
  end;

  POINT : record
    ID : NODE;
    isLeader: boolean; -- 是否是Leader
    LeaderElected: NODE;
    Point_state: Node_STATE;
  end;

--声明变量
var
  round: NUM;
  Msg : array [NODE] of MSG;
  Point : array [NODE] of POINT;
  LeaderID : NODE;

--初始化
startstate
  round := 0;
  for i: NODE do
    Msg[i].MSG_TYPE := IDLE;
    undefine Msg[i].MSG_Leader;
    Point[i].ID := i;
    Point[i].isLeader := false;
    undefine Point[i].LeaderElected;
    Point[i].Point_state := invalid;
  end;
  undefine LeaderID;
endstartstate;

ruleset i: NODE do
rule "Leader election protocol"
  Msg[i].MSG_TYPE = IDLE &
  Point[i].Point_state = invalid & 
  round = 0
==>
  Point[i].Point_state := valid;
  Msg[i].MSG_Leader := i;
  round := round + 1;
  Msg[(i % N) + 1].MSG_TYPE := ELECTION;
  Msg[(i % N) + 1].MSG_Leader := Msg[i].MSG_Leader;
  undefine LeaderID;
endrule;
endruleset;

ruleset i: NODE do
rule "Process message"
  Msg[i].MSG_TYPE = ELECTION &
  Point[i].isLeader = false
==>
  if Point[i].Point_state = invalid then
    round := round + 1;
  endif;
  if Point[i].ID > Msg[i].MSG_Leader then
    Point[i].Point_state := valid;
    Msg[i].MSG_Leader := i;
    Msg[i].MSG_TYPE := IDLE;
    Msg[(i % N) + 1].MSG_TYPE := ELECTION;
    Msg[(i % N) + 1].MSG_Leader := Msg[i].MSG_Leader;
  elsif Msg[i].MSG_Leader > Point[i].ID then
    Point[i].Point_state := valid;
    Msg[i].MSG_TYPE := IDLE;
    Msg[(i % N) + 1].MSG_TYPE := ELECTION;
    Msg[(i % N) + 1].MSG_Leader := Msg[i].MSG_Leader;
  elsif Point[i].Point_state = valid & Msg[i].MSG_Leader = Point[i].ID & Msg[i].MSG_TYPE = ELECTION then
    LeaderID := i;
    Point[i].isLeader := true;
    Point[i].LeaderElected := LeaderID;
    Msg[i].MSG_Leader := LeaderID;
    Msg[i].MSG_TYPE := LEADER;
    Msg[(i % N) + 1].MSG_Leader := LeaderID;
    Msg[(i % N) + 1].MSG_TYPE := LEADER;
  endif;
endrule;
endruleset;

ruleset i : NODE do
rule "Finish round"
  Msg[i].MSG_TYPE = LEADER &
  Point[i].Point_state = valid &
  ISUNDEFINED(Point[i].LeaderElected)
==>
  Point[i].LeaderElected := LeaderID;
  if Point[(i % N) + 1].isLeader = true then
    Msg[(i % N) + 1].MSG_TYPE := IDLE;
    undefine Msg[(i % N) + 1].MSG_Leader;
  else
    Msg[(i % N) + 1].MSG_TYPE := LEADER;
    Msg[(i % N) + 1].MSG_Leader := LeaderID;
  endif;
endrule;
endruleset;

ruleset i: NODE do
rule "Leader Invalid"
  Msg[i].MSG_TYPE = LEADER &
  Point[i].Point_state = valid &
  !ISUNDEFINED(Point[i].LeaderElected) &
  Msg[LeaderID].MSG_TYPE = IDLE
==>
  Point[i].Point_state := invalid;
  undefine Point[i].LeaderElected;
  Msg[i].MSG_TYPE := IDLE;
  round := round - 1;
  undefine Msg[i].MSG_Leader;
  if Point[(i % N) + 1].isLeader = true then
    Point[(i % N) + 1].Point_state := invalid;
    round := round - 1;
    Point[(i % N) + 1].isLeader := false;
    undefine Point[(i % N) + 1].LeaderElected;
  endif;
endrule;
endruleset;

invariant "LeaderUniqueness"
forall m: NODE do
  forall n: NODE do
    (Point[m].isLeader = true -> m = LeaderID) &
    (m != n -> Point[m].isLeader = false | Point[n].isLeader = false)
  end
end;

invariant "LeaderID is MAX"
forall m:NODE do
  forall n:NODE do
    Point[m].isLeader = true -> Point[m].ID >= Point[n].ID
  end
end;
