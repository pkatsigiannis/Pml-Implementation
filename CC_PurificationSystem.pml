mtype {EMPTY, READY, FILLED, READY_ACK, FILLING, FILLING_ACK}

mtype {STATUS_QUERY, REQ_FILLING}
mtype {STATUS_QUERY_ACK, REQ_FILLING_ACK}

mtype valve_state = EMPTY;
bool in_open = false;
bool out_open = false;

chan blue = [2] of {mtype}
chan red = [2] of {mtype}

proctype InCtrl() {
    
}

proctype OutCtrl() {
    
}

proctype Vessel() {
    
}

init {
    
}