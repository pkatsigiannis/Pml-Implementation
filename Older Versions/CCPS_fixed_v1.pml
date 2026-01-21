mtype = {
    EMPTY, READY, FILLED, // vessel state from OutValveCtrl to InValveCtrl over red channel
    STATUS_QUERY, REQ_FILLING, FILLING, // from InValveCtrl to OutValveCtrl over blue channel
    STATUS_QUERY_ACK, REQ_FILLING_ACK, FILLING_ACK, ATTENTION, // from OutValveCtrl to InValveCtrl over blue channel
    OPEN, CLOSE, // commands from controllers to valves over out_cmd and in_cmd channels
    LIQUID_QUERY // from InValveCtrl to InValve
};

// as per handout
#define liquid 1 // liquid as a constant (value irrelevant)
chan Vessel = [2] of {bit};
bool invalve_open = false; // track if InValve is open

// controller-to-controller channels
chan Blue = [2] of {mtype};
chan Red = [2] of {mtype};

// local valve command channels (sync/unbuffered)
chan In_cmd = [0] of {mtype};
chan Out_cmd = [0] of {mtype};

chan ToInValve = [1] of {mtype}; // InValveCtrl queries InValve
chan FromInValve = [1] of {bit}; // InValve reports to InValveCtrl

proctype InValveCtrl(chan blue; chan red; chan in_cmd; chan toInValve; chan fromInValve) {

    mtype current_state;
    bool liquid_detection = true;

    do
    :: blue?ATTENTION -> // respond to attention: allow new start after purification process ends
        liquid_detection = true; // ON at start

    :: liquid_detection ->
        /* Only query if we DON'T already see a report token */
        if
        :: !(fromInValve?[liquid]) ->
            toInValve!LIQUID_QUERY;
            printf("[in controller] (toInValve) sent LIQUID_QUERY\n");
        :: else -> skip
        fi;

        if
        :: fromInValve?[liquid] -> // peek for liquid (token not consumed)
            printf("[in controller] (fromInValve) liquid detected\n");
            liquid_detection = false;
            fromInValve?liquid;

            // send STATUS_QUERY to OutValveCtrl
            if 
            :: !(blue?[STATUS_QUERY]) ->
                blue!STATUS_QUERY;
                printf("[in controller] (blue) sent STATUS_QUERY\n");
            :: else -> skip; // avoid duplicates
            fi

            // wait for STATUS_QUERY_ACK and current_state
            blue?STATUS_QUERY_ACK;
            printf("[in controller] (blue) received STATUS_QUERY_ACK\n");

            // receive current_state
            red?current_state;
            printf("[in controller] (red) received current_state: %d\n", current_state);

            if
            :: current_state == EMPTY ->
                // send REQ_FILLING to OutValveCtrl
                blue!REQ_FILLING;
                printf("[in controller] (blue) sent REQ_FILLING\n");

                // wait for REQ_FILLING_ACK
                blue?REQ_FILLING_ACK;
                printf("[in controller] (blue) received REQ_FILLING_ACK\n");

                // wait for READY
                red?READY;
                printf("[in controller] (red) received READY\n");

                // send command OPEN to InValve
                in_cmd!OPEN;
                invalve_open = true;
                printf("[in controller] (in_cmd) sent OPEN\n");

                // wait for liquid to be transferred to vessel
                // InValve will send liquid when it sees OPEN and vessel is empty
                // give InValve a chance to run by checking if liquid is in vessel
                do
                :: len(Vessel) == 0 -> skip // wait for liquid
                :: len(Vessel) == 1 -> break // liquid transferred
                od;

                // notify FILLING
                blue!FILLING;
                printf("[in controller] (blue) sent FILLING\n");

                // wait for FILLING_ACK
                blue?FILLING_ACK;
                printf("[in controller] (blue) received FILLING_ACK\n");

                // wait for FILLED
                red?FILLED;
                printf("[in controller] (red) received FILLED\n");

                // send command CLOSE to InValve
                in_cmd!CLOSE;
                invalve_open = false;
                printf("[in controller] (in_cmd) sent CLOSE\n");

                // wait for ATTENTION to signal purification complete, or consume if already sent
                if
                :: blue?[ATTENTION] -> blue?ATTENTION;
                :: else -> blue?ATTENTION;
                fi;
                printf("[in controller] (blue) received ATTENTION\n");

                // clear any pending state messages from Red channel before starting new cycle
                if
                :: red?[EMPTY]; red?EMPTY;
                :: red?[READY]; red?READY;
                :: red?[FILLED]; red?FILLED;
                :: else -> skip
                fi

                // ready for new cycle
                liquid_detection = true;

            :: else -> skip; // do nothing if not EMPTY
            fi

        :: else -> skip; // wait for liquid to be reported
        fi
    od
}

proctype OutValveCtrl(chan blue; chan red; chan out_cmd; chan vessel) {
  mtype vessel_state = EMPTY;

  do
    :: blue?STATUS_QUERY ->
      printf("[out controller] (blue) received STATUS_QUERY\n");

      // ack
      blue!STATUS_QUERY_ACK;
      printf("[out controller] (blue) sent STATUS_QUERY_ACK\n");
      
      // send state
      red!vessel_state;
      printf("[out controller] (red) sent state\n");

    :: blue?REQ_FILLING ->
      printf("[out controller] (blue) received REQ_FILLING\n");

      // ack
      blue!REQ_FILLING_ACK;
      printf("[out controller] (blue) sent REQ_FILLING_ACK\n");
      
      // close out valve
      out_cmd!CLOSE;
      printf("[out controller] (out_cmd) sent CLOSE\n");

      // send READY and update state
      vessel_state = READY;
      red!vessel_state;
      printf("[out controller] (red) sent state\n");

    :: blue?FILLING ->
      printf("[out controller] (blue) received FILLING\n");

      // ack
      blue!FILLING_ACK;
      printf("[out controller] (blue) sent FILLING_ACK\n");

      // send filled
      vessel_state = FILLED;
      red!vessel_state;
      printf("[out controller] (red) sent FILLING_ACK\n");

      do
        :: len(vessel) == 1 ->
          // start draining process (wait for liquid to be in vessel)
          printf("[out controller] draining\n");

          // open out valve
          out_cmd!OPEN;
          printf("[out controller] (out_cmd) sent OPEN\n");

          vessel_state = EMPTY;

          // send empty
          red!vessel_state;
          printf("[out controller] state = EMPTY\n");

          // close out valve
          out_cmd!CLOSE;
          printf("[out controller] (out_cmd) sent CLOSE\n");

          blue!ATTENTION;
          printf("[out controller] (blue) sent ATTENTION\n");

          break;

      od
  od
}


/* 
    * Assumptions
    * 1. InValve always holds liquid.
    * 2. only 1 batch is necessary for filling the vessel
*/
proctype InValve(chan outflow; chan in_cmd; chan toInValve; chan fromInValve) {

    mtype state = CLOSE;
    mtype cmd;

    do
    :: in_cmd?cmd -> // listen for command
        if 
        :: cmd == OPEN  -> state = OPEN
        :: cmd == CLOSE -> state = CLOSE
        fi

    :: toInValve?LIQUID_QUERY -> // listen for liquid query
        if
        :: len(fromInValve) == 0 -> 
            fromInValve!liquid; //assumption: InValve always has liquid
            printf("[InValve] reported liquid present\n");
        :: else -> skip
        fi

    :: state == OPEN && len(outflow) == 0 -> // send liquid if valve is OPEN and outflow is empty
        outflow!liquid;
    od
}

proctype OutValve(chan inflow; chan out_cmd) {

    mtype state = CLOSE;
    mtype cmd;

    do
    :: out_cmd?cmd -> // listen for command
        if
        :: cmd == OPEN  -> state = OPEN
        :: cmd == CLOSE -> state = CLOSE
        fi

    :: state == OPEN && len(inflow) > 0 -> // pour liquid if valve is OPEN and inflow channel has liquid
        inflow?liquid;
    od
}

init {
    atomic {
        FromInValve!liquid; // assumption: InValve always has liquid (uncontrollable)
        run InValveCtrl(Blue, Red, In_cmd, ToInValve, FromInValve);
        run OutValveCtrl(Blue, Red, Out_cmd, Vessel);
        run InValve(Vessel, In_cmd, ToInValve, FromInValve);
        run OutValve(Vessel, Out_cmd);
    }
}

ltl p1 {[] <> (len(Vessel) == 1)} // Vessel is eventually filled
ltl p2 {[] <> (len(Vessel) == 0)} // Vessel is eventually emptied
