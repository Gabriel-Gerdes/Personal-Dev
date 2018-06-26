'------------------------------------------------------------------------------
' "annunfdx.bas", Door intercom (outside station)
'------------------------------------------------------------------------------
    DIM ver$(18)

' V00.09  11.11.06 AK    - added serial gateway function
' V00.09  12.01.07 PK+JR - buffer ballancing
' V00.09  24.01.07 PK    - send on level
'                        - serial settings for serial GW
' V00.09  14.02.07 PK    - configurable keepalive messages
' V00.09  20.02.07 PK    - simple RTP implementation, bitrate and packet size are not according to RFCs
' V00.09  21.02.07 PK    - configurable UDP/RTP mode
' V00.10  05.03.07 PK    - version string
' V00.11  05.03.07 PK    - RTP payload 20ms for 8kHz sampling frequencies
' V00.12  06.03.07 PK    - RTP payload 20ms
'                        - serial gateway send only if there's any data
'                        - Barix dynamic RTP payload types
'                        - speed optimization - 8kHz works perfectly, PCM/24 is still too slow
' V00.13  07.03.07 PK    - RTP implemented in firmware
' V00.14  10.01.08 SH/PK - implemented ABCL v0.12 IO map; button 0 (I0) now used instead of I1 to be compatible with Ann1000
' V00.15  02.01.08 PK    - txsize ignored in RTP mode
' V00.16  23.09.08 PK    - added receiving IP address
' V00.17  06.12.08 PK    - using uncompressed audio mode 11
' V00.18  12.03.09 PK    - fixed bug #057.01: broken RTP
' V00.19  16.04.09 JP    - added serial gateway functionality configurable.
'						 - implemented active TCP connection support
'                        - Relay Off delay made configurable from UI
' V00.20  16.09.09 KK    - Fixed syntax error stray : on line 232
'                        - Fixed syntax error stray : on line 246
' V00.21  03.05.10 PK    - implemented frame based buffering; delay now in ms instead of bytes
' V00.22  03.06.10 PK    - #057.08: proper defaults for Delay and Frame Duration in Annunfdx

    ver$="1.5.13"

    Dim _Mr$(4096)                                ' receiver audio buffer
    Dim l1k,x1k                                   ' routines for subroutine at 10000
    
    DIM _Ms$(1400)

    Dim _Mt$(100)

    Dim ad_gain
    Dim mic_gain
    Dim rho$(32)
	Dim tSIp$(32)
	Dim rpo
    dim com$(50)
    dim tmout 
	
	dim svrConnected
	dim savedButtonState
	dim curButtonState
	dim lastUDP
	dim x1ServerMsgPipeld,x2ServerMsgPipeld
	dim lcdM$
	dim lcdBlinkTimes, lcdUpdate, lcdHeartbeat
	dim tcpM$
	dim twiM$
	dim fasM$
	dim kepM$
	dim serialReading
	dim debug, playing, sending, receiving, conversation, talkRequest, talking, delaySending
	dim lane$(50)
	dim twiS$(50)
	dim udpI$(32)
	dim updFromPort

    'parameters for gateway
    DIM  _Mb$(1024),lb,lb2,gwprt
    DIM cnwai 'timout for active tcp connection
	
	
	'SNMP Special Veriables built in.
	dim _S01$ 'id
	dim _S02$ 'twic server name
	dim _S03$ 'firmware version

    tmout = 0 ' relay timeout
	
	lcdBlinkTimes = 0
	lcdUpdate = 0
	lcdHeartbeat = 0
	serialReading = 0
	
	debug = 0
	playing = 0
	sending = 0
	receiving = 0
	conversation = 0
	talkRequest = 0
	talking = 0
	delaySending = 0
    
    For i=1 to 50 
        midset _Mt$,2*i-1,2,&HFFFF 
    Next i     ' fill "empty" buffer with FF, this allows to fill rcv buf with val

    Open "STP:0" as 2
    read 2,set$
    Close 2

    com$="COM:"
    comb=midget(set$,82,1)
    if comb=0 then com$=com$+"38400,"
    if comb=1 then com$=com$+"19200,"
    if comb=2 then com$=com$+"9600,"
    if comb=3 then com$=com$+"4800,"
    if comb=4 then com$=com$+"2400,"
    if comb=5 then com$=com$+"1200,"
    if comb=6 then com$=com$+"600,"
    if comb=7 then com$=com$+"300,"
    if comb=8 then com$=com$+"115200,"
    if comb=9 then com$=com$+"57600,"
    if comb=10 then com$=com$+"230400,"
    if comb=11 then com$=com$+"76800,"

    comb=midget(set$,81,1)
    if and(comb,&H30)=0 then com$=com$+"N,"
    if and(comb,&H30)=&H30 then com$=com$+"E,"
    if and(comb,&H30)=&H10 then com$=com$+"O,"
    
    if and(comb,4) then com$=com$+"8," else com$=com$+"7,"

    if and(comb,128) then com$=com$+"2," else com$=com$+"1,"
    
    comb=midget(set$,83,1)
    if comb=0 then com$=com$+"NON:"
    if comb=1 then com$=com$+"SFW:"
    if comb=2 then com$=com$+"HDW:"
    if comb=8 then com$=com$+"485:"

    com$=com$+"1"   ' serial 1

    Open "STP:500" as 2
    read 2,set$
    Close 2

    vol=midget(set$,1,1)
    If vol>20 Then vol=20

    ad_gain=midget(set$,2,1)
    If ad_gain>15 Then ad_gain=15

    mic_gain=midget(set$,3,1)
    If mic_gain>15 Then mic_gain=15

    If midget(set$,11,1)=129 Then      ' input (129=line, 130=mic)
        inp=1
        stereo=0
    Else
        inp=2
        stereo=0
    endif

    enc=midget(set$,12,1)                      ' encoding

    frmsz=midget(set$,28,2)
  
    l=midget(set$,31,4)                       ' dst IP
    If l Then                                   ' if nonzero, set it
      rho$=sprintf$("%lA",l)
      rpo=midget(set$,35,2)                    ' dst port
    Else
      rho$=""
    endif                                       ' otherwise, in learn mode
    rcvaddr=midget(set$,41,4)                  ' receiving IP
    rcvip$=sprintf$("%lA",rcvaddr)
    syslog "destination IP:"+rho$

    syslog "receving IP:"+rcvip$

    port=midget(set$,37,2)                     ' listen port here (local)
    
    'gateway    parameters
    gwprt=midget(set$,109,2)
	
    'relay timout
    tmout=midget(set$,111,2)
	
	' TAP COMM
	_S03$=ver$
	Open "STP:808" as 2
    write 2,ver$,0
    Close 2
	
	Open "STP:816" as 2
    write 2,"0",0
    Close 2
	
	Open "STP:800" as 2
    read 2,set$
    Close 2
	
	debug=midget(set$,6,1)
	syslog "Debug: "+str$(debug)
	
	Open "STP:900" as 2
    read 2,set$
    Close 2
	
	lane$=mid$(set$,1,50)
	_S01$=lane$
    syslog "Lane Number:"+lane$
	
	twiS$=mid$(set$,51,50)
	_S02$=twiS$ + ":" + str$(gwprt)
    syslog "TWIC Server: "+twiS$	

    qual=&H0c08							' enc=7 for this one, but this is default (uLaw/8kHz)
    sr=8							' samples per milliseconds
    If enc=6 Then               'uLaw/24kHz
        qual=&H0c18
        sr=24							' samples per milliseconds
    endif
    If enc=8 Then               'aLaw/24kHz
        qual=&H0d18
        sr=24							' samples per milliseconds
    endif
    If enc=9 Then               'aLaw/8kHz
        qual=&H0d08
    endif
    If enc=10 Then              'PCM/24kHz
        qual=&H0e18
        sr=24							' samples per milliseconds
    endif
    If enc=11 Then              'PCM/8kHz
        qual=&H0e08
   endif
        
    'AUD:mode,flags,quality,delay,frame size in samples,ssrc"
    Set$="AUD:11,32,"+str$(qual)+","+str$(delms)+","+str$(frmsz*sr)+",1"      ' last parameter SSRC
	syslog "Audio: "+Set$
	
    Open Set$ as 7
    Write 7,str$(ad_gain),-2                                    'set A/D Gain
    Write 7,str$(mic_gain),-1                                   'set Mic Gain
    Write 7,str$(inp),-3                                'set input source to mic/line
    Write 7,str$(stereo),-4                             'set mono/stereo
    Write 7,str$(vol),-12                                       'set volume to vol
	Write 7,"2",-14                                       'microphone control, phantom power on


    Open "UDP:"+rcvip$+":"+str$(port) as 4         ' audio (listen) port
    
    on TIMER1 GOSUB 20000                       ' timing, I/O, management
    TIMER 1,100                                 ' every 100ms i/O handling

    on TIMER2 GOSUB 25200                       ' PSI Sending Audio Over UDP Timeout
    TIMER 2,30000                               ' every 30 seconds
	
	on TIMER3 GOSUB 25100                       ' PSI Heartbeat
    TIMER 3,4000                                  ' every 4 seconds
	
	on TIMER4 GOSUB 25000                       ' PSI LCD Messages
    TIMER 4,500                                  ' every half second

    '''On UDP GoSub 10000                          ' process audio input HERE

    '--- serial gateway, bgn --------------------------------------------------
    'disable gateway function if port is improper

    if and(gwprt <> 0,twiS$ <> "") then
            cnwai = _TMR_(0) + 10000
			syslog "Connecting to TWIC Server at " + twiS$ + ":" + str$(gwprt)
            open "TCP:"+twiS$+":" + str$(gwprt) as 5
			
			if connected(5)=0 then
				syslog "Could not connect to TWIC Server"
				tSIp$=""
			else
				syslog "Connected to TWIC Server at " + RMTHOST$(5) + ":" + str$(RMTPORT(5))
				tSIp$ = RMTHOST$(5)
			endif
    endif

    'open "COM:76800,N,8,1,NON:1" as 2 'open serial port for gateway
    open com$ as 2 'open serial port for the gateway
	
	savedButtonState = 1
	lastUDP=0
	
	' wait for the LCD screen to start up
	'delay 2000
	
	syslog "Let's Go!!!!"
	
	' send the lane id
	write 2, "["+lane$+"]", 0

	delay 500
	
	' set the displays state to connected or not connected
	svrConnected = connected(5)
	if svrConnected then
		write 2, "\x06", 0
		write 5, lane$+":Connected\n", 0
		
		Open "STP:816" as 6
		write 6,"1",0
		Close 6
	else
		write 2, "\x15", 0
		
		Open "STP:816" as 6
		write 6,"0",0
		Close 6
	endif

    '--- serial gateway, end --------------------------------------------------

100
    'in case of tcp active connection
	if cnwai < _TMR_(0) then
		
		if and(gwprt <> 0,twiS$ <> "",connected(5) = 0 ) then
			if mediatype(5) then close 5

			if debug=1 then syslog "Serial Gateway: Active TCP connection reopening with " + twiS$ + ":" + str$(gwprt)
			open "TCP:"+twiS$+":"+ str$(gwprt) as 5 
			
			if connected(5)=0 then
				if debug=1 then syslog "Could not connect to TWIC Server"
				tSIp$ = ""
			else
				if debug=1 then syslog "Connected to TWIC Server at " + RMTHOST$(5) + ":" + str$(RMTPORT(5))
				tSIp$ = RMTHOST$(5)
			endif
		endif
		
		if svrConnected <> connected(5) then
			' set the displays state to connected or not connected
			svrConnected = connected(5)
			if svrConnected then
				write 2, "\x06", 0
				write 5, lane$+":Connected\n", 0
				
				Open "STP:816" as 6
				write 6,"1",0
				Close 6
			else
				write 2, "\x15", 0
				
				Open "STP:816" as 6
				write 6,"0",0
				Close 6
			endif
		endif
		
		cnwai = _TMR_(0) + 10000
	endif

    gosub 5000
	
	' button press
	curButtonState = iostate(201)
	if and(curButtonState=0, savedButtonState=1) then
		savedButtonState=0
		if connected(5) then write 5, lane$+":Button:Call\n", 0
	endif
	if curButtonState=1 then savedButtonState=1
	
	' LCD Updates
	if lcdUpdate>0 then
		
		if lcdUpdate=1 then write 2,"~",0
		if lcdUpdate=2 then write 2,"||",0
		if lcdUpdate=3 then write 2,"|"+lcdM$+"|",0
		
		lcdUpdate=0
	endif
	
	if lcdHeartbeat=1 then
		write 2, "\x07", 0
		lcdHeartbeat=0
	endif

    if talkRequest>0 then
		talkRequest=talkRequest-1
	endif
	
    l1k=lastlen(4)
    if l1k<0 then
		gosub 10000
	else
		if and(debug=1,playing=1) then syslog "Done Playing Audio"
		if playing>0 then playing=playing-1
	endif

    read 7,_Ms$                                 ' read one frame - always - if availabe (to keep buf empty)
    l=lastlen(7)
	
	' no audio data, don't try to send audio
	' cannot send if no address
	' don't send audio if we were told to stop
    if or(l=0,Len(rho$)=0,lastUDP=0,tSIp$=rho$) Then
		if and(debug=1,sending=1) then syslog "Done Sending Audio"
		if sending>0 then sending=sending-1
		if lastUDP=0 then delaySending=50		' set a timeout so we don't send the last thing that we played
		GoTo 100
	else
		if and(debug=1,sending=0) then syslog "Start Sending Audio"
		sending=200
		if delaySending=0 then				' don't send the last thing we played
			write 4,_Ms$,l,rho$,rpo
		else
			delaySending=delaySending-1
		endif
	endif

    GoTo 100

10000
	udpI$ = rmthost$(4)
	updFromPort = rmtport(4)
	
	' pull the UDP data first
	read 4,_Mr$
	
	if and(debug=1,receiving=0) then syslog "Start receiving UDP from: "+udpI$
	receiving=5
	
	if udpI$=tSIp$ then	' is this the twic server?
		if conversation>0 then return	' we are in a conversation and the server is trying to talk, ignore him
	else
		' its not the twic server, get UDP address
		rho$=udpI$
		rpo=updFromPort
		if and(debug=1,conversation=0) then syslog "New conversation with " + rho$ + ":" + str$(rpo)
		conversation=10 
	endif
	
	If l1k>-12 Then
	return                                      ' presumably keepalive, not enough data
	endif

	if and(lastUDP=0, udpI$<>tSIp$, midget(_Mr$,1,1)=1, midget(_Mr$,2,1)=1, midget(_Mr$,3,1)=1, midget(_Mr$,4,1)=1, midget(_Mr$,5,1)=1, midget(_Mr$,6,1)=1, midget(_Mr$,7,1)=1, midget(_Mr$,8,1)=1) Then
		lastUDP=1
		talkRequest=10
		talking=1
		if debug=1 then syslog "Got a start talking message"
	else
		If and(talkRequest=0, lastUDP=1, udpI$<>tSIp$) then		' if we got audio data that's not ones, and we are talking, and we weren't just asked to start talking, then stop talking
			lastUDP=0
			talking=0
			if debug=1 then syslog "Got a stop talking message"
		endif
	endif

	if and(debug=1,playing=0) then syslog "Start Playing Audio"
	playing=100
	Write 7,_Mr$,-l1k                          ' output audio
	return

25200
	if talking=1 then 	' the talking flag is set when we are told to talk, unset the flag
		talking=0
	else
		if and(talking=0,lastUDP=1) then 	' its been at least 30 seconds since we were told to talk and we haven't been told to stop talking
			lastUDP=0						' we assume that no one is going to tell us to stop talking, so we stop on our own
			if debug=1 then syslog "Sending audio timeout. Force stop sending audio."
		endif
	endif
	return

20000
	if receiving>0 then receiving=receiving-1
	if and(debug=1,receiving=1) then syslog "Done receiving UDP"
	
	if lastUDP=0 then
		if conversation>0 then
			conversation=conversation-1
			if conversation=0 then
				rho$=""
				if debug=1 then syslog "Conversation over, clearing partner address"
			endif
		endif
	endif
	return
	  
4000 
    'TCP Gateway begin-------------------------------------------------
	read 2, _Mb$
	if debug=1 then syslog "From Uno: "+_Mb$
	
	twiM$ = twiM$ + _Mb$
	twicStart = instr(1, twiM$, "{")
	twicEnd = instr(1, twiM$, "}")
	
	if twicStart > 0 then
		if twicEnd > twicStart then
			twiM$ = mid$(twiM$, twicStart+1, twicEnd-twicStart-1)
			if debug=1 then syslog "TWIC Msg: "+twiM$
			if connected(5) then write 5,lane$+":TwicNum:"+twiM$+"\n",0
			twiM$ = ""
        else
            if debug=1 then syslog "TWIC Buffer: "+twiM$
            if len(twiM$)>50 then twiM$ = ""
		endif
	else
		twiM$ = ""
	endif
	
	fasM$ = fasM$ + _Mb$	
	fascnStart = instr(1, fasM$, "(")
	fascnEnd = instr(1, fasM$, ")")
	
	if fascnStart > 0 then
		if fascnEnd > fascnStart then
			fasM$ = mid$(fasM$, fascnStart+1, fascnEnd-fascnStart-1)
			if debug=1 then syslog "FASCN Msg: "+fasM$
			if and(connected(5), len(fasM$)=50) then write 5,lane$+":FASCN:"+fasM$+"\n",0
			fasM$ = ""
        else
            if debug=1 then syslog "FASCN Buffer: "+fasM$
            if len(fasM$)>50 then fasM$ = ""
		endif
	else
		fasM$ = ""
	endif
	
	kepM$ = kepM$ + _Mb$	
	kaypadStart = instr(1, kepM$, "<")
	keypadEnd = instr(1, kepM$, ">")
	
	if kaypadStart > 0 then
		if keypadEnd > kaypadStart then
			kepM$ = mid$(kepM$, kaypadStart+1, keypadEnd-kaypadStart-1)
			if debug=1 then syslog "Keypad Msg: "+kepM$
			if connected(5) then write 5,lane$+":KEYPAD:"+kepM$+"\n",0
			kepM$ = ""
        else
            if debug=1 then syslog "KEYPAD Buffer: "+kepM$
            if len(kepM$)>50 then kepM$ = ""
		endif
	else
		kepM$ = ""
	endif
	
    return
4010
	read 5,_Mb$
	if debug=1 then syslog "From Server:" + _Mb$
	
	tcpM$ = _Mb$
	newLineIdx = instr(1,tcpM$,"\n")
	if newLineIdx = 0 then return
	
	tcpM$ = mid$(tcpM$,1,newLineIdx-1)
	if debug=1 then syslog "TCP Msg: "+tcpM$
	
	' find the indexes of the two pipe characters, return if there aren't at least 2
	x1ServerMsgPipeld = instr(1, tcpM$, "|")
	x2ServerMsgPipeld = instr(x1ServerMsgPipeld+1, tcpM$, "|")
	if x2ServerMsgPipeld=0 then return
	
	' parse out the command and two data elements
	serverMsgCmd$ = mid$(tcpM$, 1, x1ServerMsgPipeld-1)
	serverMsgData1$ = mid$(tcpM$, x1ServerMsgPipeld+1, x2ServerMsgPipeld - x1ServerMsgPipeld - 1)
	serverMsgData2$ = mid$(tcpM$, x2ServerMsgPipeld+1)
	
	if debug=1 then syslog "Cmd:" + serverMsgCmd$
	
	if serverMsgCmd$ = "LCDSHOW" then
		lcdM$ = serverMsgData1$
		write 2,"|"+lcdM$+"|",0
		lcdBlinkTimes = val(serverMsgData2$) * 4
	endif
	
	if serverMsgCmd$ = "LCDERROR" then
		write 2,"`"+serverMsgData1$+"`",0
	endif
	
	if serverMsgCmd$ = "RELAY" then
		if serverMsgData1$ = "OPEN" then
			if debug=1 then syslog "Opening Relay"
			IOCTL 1, 0
		endif
		
		if serverMsgData1$ = "CLOSE" then
			if debug=1 then syslog "Closing Relay"
			IOCTL 1, 1
		endif
		
		if serverMsgData1$ = "PULSE" then
			if debug=1 then syslog "Closing Relay"
			IOCTL 1, 1
			delay val(serverMsgData2$)
			if debug=1 then syslog "Opening Relay"
			IOCTL 1, 0
		endif
	endif
	
	tcpM$ = ""
	
    return  
'TCP Gateway ends --------------------------------------------------

5000
	if filesize(2) then gosub 4000
	
	if not(connected(5)) then return
	if filesize(5)  then gosub 4010 
return

25000
	if lcdBlinkTimes > 0 then
		lcdBlinkTimes = lcdBlinkTimes - 1
		
		if lcdBlinkTimes = 0 then
			lcdUpdate = 1
			return
		endif
		
		if lcdBlinkTimes%4 = 0 then
			lcdUpdate = 2
			return
		endif
		
		lcdUpdate = 3
		
	endif
return

25100
	lcdHeartbeat=1
return