const
  N: 8;  -- 环上的节点数

type
  NODE : 0..N;
  STATE: enum {IDLE, ELECTION, LEADER}; -- 节点状态
  Node_V : enum {valid, invalid};

  MSG : record
    MSG_TYPE: STATE;
    MSG_Leader : NODE;
  end;

--声明变量
var
  round: 1..N;
  LeaderID: 0..N;
  leaderElected: boolean; -- 是否选出了Leader
  Point_state: array [NODE] of Node_V;
  Msg : array [NODE] of MSG;

--初始化
startstate
  round := 1;
  for i: NODE do
    Msg[i].MSG_TYPE := IDLE;
    Point_state[i] := invalid;
    Msg[i].MSG_Leader := 0;
  end;
  leaderElected := false;
endstartstate;

ruleset i: NODE do
rule "Leader election protocol"
  Msg[i].MSG_TYPE = IDLE &
  Point_state[i] = invalid &
  leaderElected = false &
  round != N
==>
  Point_state[i] := valid;
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
  Point_state[i] = valid &
  leaderElected = false &
  round != N
==>
  if i >= Msg[i].MSG_Leader then
    Msg[i].MSG_Leader := i;
    LeaderID:= i;
  endif;
endrule;
endruleset;

ruleset i : NODE do
rule "Finish round"
  Msg[i].MSG_TYPE = ELECTION &
  Point_state[i] = valid &
  leaderElected = false &
  Msg[i].MSG_Leader = i
==>
  Msg[i].MSG_Leader := LeaderID;
  Msg[i].MSG_TYPE := IDLE;
  leaderElected := true;
  Msg[LeaderID].MSG_TYPE := LEADER;
endrule;
endruleset;

ruleset i: NODE do
rule "Leader Invalid"
  Msg[i].MSG_TYPE = LEADER &
  Point_state[i] = invalid &
  leaderElected = true
==>
  Msg[(LeaderID % N) + 1].MSG_TYPE := ELECTION;
  leaderElected := false;
  round := 1;
  undefine Msg[i].MSG_Leader;
  undefine LeaderID;
endrule;
endruleset;

invariant "LeaderUniqueness"
forall m: NODE do
  forall n: NODE do
    (m != n -> (Msg[m].MSG_TYPE != LEADER | Msg[n].MSG_TYPE != LEADER | m = n)) & 
    ((leaderElected = true & m != n) -> (Msg[m].MSG_Leader = Msg[n].MSG_Leader)) 
  end
end;
