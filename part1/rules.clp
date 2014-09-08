
(defrule begin
	?init<-(initial-fact)
	=>
	(retract ?init)
	;(assert (time-now 0)) ;to control current time fact
	;(assert (temp 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32 33 34 35 36 37 38 39 40 41 42 43 44 45 46 47 48 49 50
	;51 52 53 54 55 56 57 58 59 60 61 62 63 64 65 66 67 68 69 70 71 72 73 74 75 76 77 78 79 80 81 82 83 84 85 86 87 88 89 90 91 92 93 94 95 96 97 98 99 100
	;101 102 103 104 105 106 107 108 109 110 111 112 113 114 115 116 117 118 119 120 121 122 123 124 125 126 127 128 129 130 131 132 133 134 135 136 137 138 
	;139 140 141 142 143 144 145 146 147 148 149 150 151 152 153 154 155 156 157 158 159 160 161 162 163 164 165 166 167 168 169 170 171 172 173 174 175 176 177 
	;178 179 180 181 182 183 184 185 186 187 188 189 190 191 192 193 194 195 196 197 198 199 200 201 202 203 204 205 206 207 208 209 210 211 212 213 214 215 216
	;217 218 219 220 221 222 223 224 225 226 227 228 229 230 231 232 233 234 235 236 237 238 239 240 241 242 243 244 245 246 247 248 249 250 251 252 253 254 255 
	;256 257 258 259 260 261 262 263 264 265 266 267 268 269 270)) ;to control package assignment
	(assert (temp2 1)) ;to control entry of time in event fact
	(assert (event 1)) ;to control order of occurrence 
	(assert (current-time 0))
	(assert (origin "Orlando"))
	(assert (package-checked))
	(assert (order-available 0)) 
	(assert (report-generation false))
)



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;get package order ;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule get-package-order 
	?clock <- (current-time ?x)
	?order <- (order-available ?)
	?p-check <- (package-checked $?assigned)
	(package (number ?no&:(not (member ?no $?assigned))) (arrival-time ?next))
	(not (package (number ?n&:(not (member ?n $?assigned))) (arrival-time ?time&:(< ?time ?next))))
	(not (package (number ?nm&:(not (member ?nm $?assigned))&:(< ?nm ?no)) (arrival-time ?time1&:(= ?time1 ?next))))
	=>
	(retract ?clock ?order ?p-check)
	(assert (order-available ?no))
	(assert (package-checked $?assigned ?no)) 
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;assign package to truck;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule pickup-after-waiting
	?order<-(order-available ?no&:(> ?no 0))
	;(current-time ?cur-time)
	;?e <- (event ?e1 $?evt)
	(package (number ?no)  
			(depart-city ?dep-city) 
			(delivery-city ?del-city) 
			(size ?sz) 
			(arrival-time ?at))
	?tr <- (truck (truck-no ?num)
					(current-city ?cur-city)
					(destination ?dest) 
					(available-space ?space&:(>= ?space ?sz)) 
					(current-action "idle") 
					(current-time ?ct) 
					(last-run ?last&:(< ?last ?at))
					)
	(not (truck (available-space ?sp&:(>= ?sp ?sz)) (current-action "idle") (last-run ?last1&:(< ?last1 ?last))))
	(not (truck (truck-no ?n1&:(< ?n1 ?num)) (available-space ?sp1&:(>= ?sp1 ?sz)) (current-action "idle") (last-run ?last2&:(= ?last2 ?last))))
	?t-report <- (truck-report (truck-number ?num)
								(total-wait-time ?twt) 
								(time-on-road ?tor) 
								(percent-busy-time ?pbt)
								(packages-transported ?pt) 
								(avg-%-of-space-occupied ?so) 
								(non-delivery-time ?ndt)
								(%-time-delivering ?ptd)) 
	?p-report <- (package-report (package-number ?no) 
									(wait-time ?))
	?p-in <-(p-info (p-no ?no) (wait-time ?wt)) 
	(test (< (- ?last ?at) 0))
	=>
	(retract ?order ?tr ?t-report ?p-report ?p-in) 
	(bind ?wait (- ?at ?last))
	(assert (truck-report (truck-number ?num) 
							(total-wait-time =(+ ?twt ?wait)) 
							(time-on-road ?tor) 
							(percent-busy-time ?pbt)
							(packages-transported =(+ ?pt 1)) 
							(avg-%-of-space-occupied =(+ ?so ?sz)) 
							(non-delivery-time ?ndt)
							(%-time-delivering ?ptd)))
	(assert (p-info (p-no ?no) (wait-time ?wt) (assigned-at =(+ ?wt ?at))))
	(assert (package-report (package-number ?no) (wait-time ?wt)))
	(assert (truck (truck-no ?num) 
					(current-city ?cur-city) 
					(destination ?dep-city) 
					(available-space ?space) 
					(current-action "going to pick up") 
					(current-time ?at)  
					(package-carried ?no)
					(occupied-space ?sz)
					)) 	
	(assert (cheapest-route (start ?cur-city) (stop ?dep-city) (lowest-cost -1)))
	(assert (find-distance))
	(assert (current-time ?at))
	;(assert (event $?evt))
	(assert (order-available 0))
)

(defrule pickup-without-waiting
	?order<-(order-available ?no&:(> ?no 0))
	;(current-time ?cur-time)
	;?e <- (event ?e1 $?evt)
	(package (number ?no)  
			(depart-city ?dep-city) 
			(delivery-city ?del-city) 
			(size ?sz) 
			(arrival-time ?at))
	?tr <- (truck (truck-no ?num)
					(current-city ?cur-city)
					(destination ?dest) 
					(available-space ?space&:(>= ?space ?sz)) 
					(current-action "idle") 
					(current-time ?ct)
					(last-run ?last&:(>= ?last ?at))
					)
	(not (truck (available-space ?sp&:(>= ?sp ?sz)) (current-action "idle") (last-run ?last1&:(< ?last1 ?last))))
	(not (truck (truck-no ?n1&:(< ?n1 ?num)) (available-space ?sp1&:(>= ?sp1 ?sz)) (current-action "idle") (last-run ?last2&:(= ?last2 ?last))))
	?t-report <- (truck-report (truck-number ?num)
								(total-wait-time ?twt) 
								(time-on-road ?tor) 
								(percent-busy-time ?pbt)
								(packages-transported ?pt) 
								(avg-%-of-space-occupied ?so) 
								(non-delivery-time ?ndt)
								(%-time-delivering ?ptd)) 
	?p-report <- (package-report (package-number ?no) 
									(wait-time ?))
	?p-in <-(p-info (p-no ?no) (wait-time ?wt)) 
	(test (>= (- ?last ?at) 0))
	=>
	(retract ?order ?tr ?t-report ?p-report ?p-in) 
	(bind ?wt (- ?last ?at))
	(assert (truck-report (truck-number ?num) 
							(total-wait-time ?twt) 
							(time-on-road ?tor) 
							(percent-busy-time ?pbt)
							(packages-transported =(+ ?pt 1)) 
							(avg-%-of-space-occupied =(+ ?so ?sz)) 
							(non-delivery-time ?ndt)
							(%-time-delivering ?ptd)))
	(assert (p-info (p-no ?no) (wait-time ?wt) (assigned-at =(+ ?wt ?at))))
	(assert (package-report (package-number ?no) (wait-time ?wt)))
	(assert (truck (truck-no ?num) 
					(current-city ?cur-city) 
					(destination ?dep-city) 
					(available-space ?space) 
					(current-action "going to pick up") 
					(current-time ?at)  
					(package-carried ?no)
					(occupied-space ?sz)
					)) 	
	(assert (cheapest-route (start ?cur-city) (stop ?dep-city) (lowest-cost -1)))
	(assert (find-distance))
	(assert (current-time ?at))
	;(assert (event $?evt))
	(assert (order-available 0))
)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;send truck to pick up package;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule pickup-package
	(package (number ?no) 
					(depart-city ?dep-city) 
					(delivery-city ?del-city) 
					(size ?sz) 
					(arrival-time ?at)
					(expected-delivery-time ?edt)
					(delivery-status ?d-stat))	
	?tr <-(truck (truck-no ?num) 
					(current-city ?cur-city) 
					(destination ?dep-city) 
					(available-space ?space)
					(current-action "going to pick up") 
					(current-time ?ct)  
					(package-carried ?no)
					)
	(p-info (p-no ?no) (wait-time ?wt))
	?ro <-(cheapest-route (start ?cur-city) (stop ?dep-city) (lowest-cost ?c&:(>= ?c 0)))
	?t-report <- (truck-report (truck-number ?num)
								(total-wait-time ?twt) 
								(time-on-road ?tor) 
								(percent-busy-time ?pbt)
								(packages-transported ?pt) 
								(avg-%-of-space-occupied ?so) 
								(non-delivery-time ?ndt)
								(%-time-delivering ?ptd)) 
	?p-report <- (package-report (package-number ?no) 
									(wait-time ?wt)
									(pick-up-time ?)) 
	=>
	(retract ?tr ?ro ?t-report ?p-report)
	(bind ?pn (str-cat "for" ?no))
	(bind ?arr-time (+ ?at ?wt))
	(bind ?arr-time2 (+ ?arr-time ?c))
	(bind ?actual-wait (+ ?wt ?c))
	(assert (package-report (package-number ?no) 
							(wait-time ?actual-wait) 
							(pick-up-time ?arr-time2)))
	(bind ?non-del (- ?arr-time2 ?arr-time))
	(assert (truck-report (truck-number ?num) 
							(total-wait-time ?twt) 
							(time-on-road ?tor) 
							(percent-busy-time ?pbt)
							(packages-transported ?pt) 
							(avg-%-of-space-occupied ?so) 
							(non-delivery-time =(+ ?non-del ?ndt))
							(%-time-delivering ?ptd)))
	(assert (s-table (time ?arr-time) 
						(p-no ?no) 
						(tr-no ?num) 
						(action "dispatched") 
						(location ?dep-city) 
						(arrival-time ?arr-time2)))
	(assert	(truck (truck-no ?num) 
					(current-city ?dep-city) 
					(destination ?del-city) 
					(available-space ?space)
					(current-action "in-transit") 
					(current-time ?arr-time2)  
					(package-carried ?no)
					))	
	(assert (cheapest-route (start ?dep-city) (stop ?del-city) (lowest-cost -1)))
	(assert (find-distance))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;deliver package to its destination;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule deliver
	(origin ?or)
	(package (number ?no) 
					(depart-city ?dep-city) 
					(delivery-city ?del-city) 
					(size ?sz) 
					(arrival-time ?at)
					(expected-delivery-time ?edt)
					(delivery-status ?d-stat))	
	?tr <- (truck (truck-no ?num) 
					(current-city ?dep-city) 
					(destination ?del-city) 
					(available-space ?space)
					(current-action "in-transit") 
					(current-time ?ct)  
					(package-carried ?no)
					(last-run ?last))
	?ro <-(cheapest-route (start ?dep-city) (stop ?del-city) (lowest-cost ?c&:(>= ?c 0)))
	?t-report <- (truck-report (truck-number ?num)
								(total-wait-time ?twt) 
								(time-on-road ?tor) 
								(percent-busy-time ?pbt)
								(packages-transported ?pt) 
								(avg-%-of-space-occupied ?so) 
								(non-delivery-time ?ndt)
								(%-time-delivering ?ptd)) 
	?p-report <- (package-report (package-number ?no) 
									(wait-time ?wt)
									(pick-up-time ?put)
									(delivery-time ?) 
									(delivered-on-time ?)
									(delivered-how-late ?)) 
	=>
	(retract ?tr ?ro ?t-report ?p-report)
	(bind ?a-time (+ ?ct ?c))
	(if (> ?a-time ?edt)
		then
		(bind ?l "late")
		(bind ?l-time (- ?a-time ?edt))
		else
		(bind ?l "on-time")
		(bind ?l-time 0)
	)
	(bind ?busy-del (- ?a-time ?ct))
	(assert (package-report (package-number ?no) 
							(wait-time ?wt) 
							(pick-up-time ?put)
							(delivery-time ?a-time)
							(delivered-on-time ?l)
							(delivered-how-late ?l-time)))
	(assert (truck-report (truck-number ?num) 
							(total-wait-time ?twt) 
							(time-on-road ?tor) 
							(percent-busy-time =(+ ?busy-del ?pbt))
							(packages-transported ?pt) 
							(avg-%-of-space-occupied ?so) 
							(non-delivery-time ?ndt)
							(%-time-delivering ?ptd)))
	(assert (s-table (time ?ct) 
						(p-no ?no) 
						(tr-no ?num) 
						(action "delivering") 
						(location ?del-city) 
						(arrival-time ?a-time)))
	(assert	(truck (truck-no ?num) 
					(current-city ?del-city) 
					(destination ?or) 
					(available-space ?space)
					(current-action "return-back-to-base") 
					(current-time ?a-time)  
					(package-carried ?no)
					))	
	(assert (cheapest-route (start ?del-city) (stop ?or) (lowest-cost -1)))
	(assert (find-distance))	
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;return back to origin;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule return-back
	(origin ?or)
	(package (number ?no) 
					(depart-city ?dep-city) 
					(delivery-city ?del-city) 
					(size ?sz) 
					(arrival-time ?at)
					(expected-delivery-time ?edt)
					(delivery-status ?d-stat))	
	?tr <- (truck (truck-no ?num) 
					(current-city ?del-city) 
					(destination ?or) 
					(available-space ?space)
					(current-action "return-back-to-base") 
					(current-time ?ct)  
					(package-carried ?no)
					(last-run ?last))
	?ro <-(cheapest-route (start ?del-city) (stop ?or) (lowest-cost ?c&:(>= ?c 0)))
	?t-report <- (truck-report (truck-number ?num)
								(total-wait-time ?twt) 
								(time-on-road ?tor) 
								(percent-busy-time ?pbt)
								(packages-transported ?pt) 
								(avg-%-of-space-occupied ?so) 
								(non-delivery-time ?ndt)
								(%-time-delivering ?ptd)) 
	(p-info (p-no ?no) (assigned-at ?ast))
	=>
	(retract ?tr ?ro ?t-report)
	(bind ?a-time (+ ?ct ?c))
	(bind ?non-del (- ?a-time ?ct))
	(bind ?busy-time (- ?a-time ?ast))
	(assert (truck-report (truck-number ?num) 
							(total-wait-time ?twt) 
							(time-on-road =(+ ?busy-time ?tor)) 
							(percent-busy-time ?pbt)
							(packages-transported ?pt) 
							(avg-%-of-space-occupied ?so) 
							(non-delivery-time =(+ ?non-del ?ndt))
							(%-time-delivering ?ptd)))
	(assert (s-table (time ?ct) 
						(p-no "none") 
						(tr-no ?num) 
						(action "return-back") 
						(location ?or) 
						(arrival-time ?a-time)))
	(assert	(truck (truck-no ?num) 
					(current-city ?or) 
					(destination none) 
					(available-space ?space)
					(current-action "idle") 
					(current-time ?a-time)  
					(package-carried "none")
					(occupied-space none)
					(last-run ?a-time))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;controlling clock event;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;if nothing else is happening increase the time
;(defrule change-clock
;	(declare (salience -50))
;	?clock <- (current-time ?ct)
;	(temp $?evt)
;	?et <- (event ?e1&: (member ?e1 $?evt))
;	(not (event ?e2&:(< ?e2 ?e1))) 
;	=>
;	(retract ?clock ?et)
;	(assert (current-time ?e1))
;	)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;finding least cost path;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defrule initial-route
 (declare (salience 2))
 (cheapest-route (start ?x)) 
 (find-distance)
 => 
 (assert (route (nodes ?x) (cost 0)))
 )
 
(defrule extended-route 
 (declare (salience 2))
 (route (nodes $?n ?y) (cost ?w)) 
 (find-distance)
 (distance (from ?y) (to ?z & ~?y & :(not (member ?z $?n))) (cost ?we)) 
 => 
 (assert (route (nodes $?n ?y ?z) (cost (+ ?w ?we))))
 ) 
 
(defrule prune-not-required-route 
 (declare (salience 10))
 (find-distance) 
 (route (nodes $? ?x) (cost ?w1)) 
 ?f <- (route (nodes $? ?x) (cost ?w2&:(> ?w2 ?w1))) 
 => 
 (retract ?f)
 ) 
 
(defrule cal-cheapest-route 
 (declare (salience 1))
 ?f <- (find-distance) 
 ?cp <- (cheapest-route (start ?y) (stop ?x)) 
 ?r <- (route (nodes $?n ?x) (cost ?w))  
 => 
 (retract ?f ?cp ?r)
 (assert (cheapest-route (start ?y) (stop ?x) (lowest-cost ?w)))
 ;(printout t crlf "route " (create$ $?n ?x) crlf "cost " ?w crlf)
 ) 

(defrule remove-path
 (declare (salience 1))
 ?r <-(route)
 =>
 (retract ?r)			
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;control routing of packages and report generation;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defrule end-routing 
	(package-checked $?assigned)
	(package (number ?no&:(member ?no $?assigned)))		
	(not (package (number ?no1&:(not (member ?no1 $?assigned)))))
	(truck (truck-no ?tr-no) (current-action "idle"))	
	(not (truck (truck-no ?n) (current-action ?act&:(neq ?act "idle"))))
	?r<-(report-generation false)
	=>
	(retract ?r)
	(assert (report-generation true))
	(open "s-table.txt" sim "a")
	(printout sim "Report Generated:" crlf " Time		Package No.		Truck No.		Action		   Location		    Arrival Time " crlf)
	(close sim)
)



(defrule report
	(declare (salience -20))
	(report-generation true)
	?simu <-(s-table (time ?time1) (p-no ?p-no) (tr-no ?t-no) (action ?act) (location ?city) (arrival-time ?a-time))
	(not (s-table (time ?time2&:(< ?time2 ?time1))))
	(not (s-table (time ?time2&:(= ?time2 ?time1)) (arrival-time ?arr-time&:(< ?arr-time ?a-time))))
	=>
	(retract ?simu)
	(open "s-table.txt" sim "a")
	(if (eq ?act "return-back")
		then
		(if (or (eq ?city "Orlando") (eq ?city "Ocala") (eq ?city "Miami") (eq ?city "Tampa"))
			then
			(printout sim "  "?time1 "		" ?p-no "			" ?t-no "			" ?act "		" ?city "				" ?a-time crlf)
			else
			(printout sim "  "?time1 "		" ?p-no "			" ?t-no "			" ?act "		" ?city "			    " ?a-time crlf)
		)
		else
		(if (or (eq ?city "Orlando") (eq ?city "Ocala") (eq ?city "Miami") (eq ?city "Tampa"))
			then		
			(printout sim "  "?time1 "		" ?p-no "			" ?t-no "			" ?act "		    " ?city "				" ?a-time crlf)
			else
			(printout sim "  "?time1 "		" ?p-no "			" ?t-no "			" ?act "		    " ?city "			    " ?a-time crlf)
		)
	)
	(close sim) 
)
	
(defrule print-p-report
	(declare (salience -20))
	?r<-(report-generation true)
	=>
	(retract ?r)
	(assert (print-p-report true))
	(assert (temp1 1))	
	(open "s-table.txt" sim "a")
	(printout sim crlf "Package Report:" crlf "   Number   	Wait Time    	Pick-Up Time	 Delivery Time	  Delivery-Status  Late Time" crlf)
	(close sim)
)

(defrule package-report
	(print-p-report true)
	?t<-(temp1 ?no)
	(package-report (package-number ?no) (wait-time ?wt) (pick-up-time ?pu) (delivery-time ?dt) (delivered-on-time ?dot) (delivered-how-late ?dhl))
	=>
	(retract ?t)
	(assert (temp1 =(+ ?no 1)))
	(open "s-table.txt" sim "a")
	(printout sim " "?no "		" ?wt "		" ?pu "		" ?dt "		" ?dot "		  " ?dhl crlf)
	(close sim)
)

(defrule p-avg-report
	(declare (salience -20))
	?p<-(print-p-report true)
	=>
	(retract ?p)
	(assert (cal-p-avg-report true))
	(open "s-table.txt" sim "a")
	(printout sim crlf "Average Report of packages:" crlf "Avg-Wait-Time       Packages on-time		   Packages late		      Avg-Lateness-of-late-packages	     Avg-Lateness-of-all-packages" crlf)
	(close sim)
	(assert (temp3 1))
)

(defrule calculate-avg-report
	?t3<-(temp3 ?no)
	(cal-p-avg-report true)
	(package-report (package-number ?no) (wait-time ?wt) (delivered-on-time ?dot) (delivered-how-late ?dhl))
	?p-avg<-(avg-package-report (avg-wait-time ?avg-wt) (packages-delivered-on-time ?pdot) (packages-delivered-late ?pdl) (avg-lateness-of-late-packages ?avg-l) (avg-lateness-of-all-packages ?avg-l-all))
	=>
	(retract ?t3 ?p-avg)
	(assert (temp3 =(+ ?no 1)))
	(bind ?avg-wt (+ ?avg-wt ?wt))
	(if (eq ?dot "on-time")
		then
		(bind ?pdot (+ ?pdot 1))
		else
		(bind ?pdl (+ ?pdl 1))
	)
	(bind ?avg-l (+ ?avg-l ?dhl))
	(assert (avg-package-report (avg-wait-time ?avg-wt) (packages-delivered-on-time ?pdot) (packages-delivered-late ?pdl) (avg-lateness-of-late-packages ?avg-l) (avg-lateness-of-all-packages ?avg-l-all)))	
)

(defrule print-avg-report
	(declare (salience -20))
	?p<-(cal-p-avg-report true)
	?p-avg<-(avg-package-report (avg-wait-time ?avg-wt) (packages-delivered-on-time ?pdot) (packages-delivered-late ?pdl) (avg-lateness-of-late-packages ?avg-l) (avg-lateness-of-all-packages ?avg-l-all))
	=>	
	(retract ?p ?p-avg)
	(assert (start-tr true))
	(bind ?t (+ ?pdot ?pdl))
	(bind ?avg-wt (/ ?avg-wt ?t))
	(bind ?avg-l-all (/ ?avg-l ?t))
	(bind ?avg-l (/ ?avg-l ?pdl))
	(assert (avg-package-report (avg-wait-time ?avg-wt) (packages-delivered-on-time ?pdot) (packages-delivered-late ?pdl) (avg-lateness-of-late-packages ?avg-l) (avg-lateness-of-all-packages ?avg-l-all)))
	(open "s-table.txt" sim "a")
	(printout sim "	"?avg-wt "			" ?pdot "				" ?pdl "				" ?avg-l "		    	" ?avg-l-all  crlf)
	(close sim)
)

(defrule truck-report
	(declare (salience -20))
	?s<-(start-tr true)
	=>
	(retract ?s)
	(assert (begin-tr-rep true))
	(open "s-table.txt" sim "a")
	(printout sim crlf "Truck Report:" crlf "Number  Total-Wait-Time	 Total-Busy-Time	%-Busy-Time	 Packages-Transported   Avg-%-Truck-Occupied   Non-delivery-Travel-Time	  %-Busy-Time-spent-delivering" crlf)
	(close sim)
)

(defrule truck-cal
	?t<-(begin-tr-rep true)
	(truck (truck-no ?t-no) (last-run ?lr))
	(not (truck (truck-no ?no) (last-run ?last1&:(> ?last1 ?lr))))
	=>
	(retract ?t)
	(assert (start-cal true))
	(assert (final ?lr))
	(assert (check))
)

(defrule truck-calc
	(start-cal true)
	(final ?f)
	?t<-(check  $?ch)
	(truck (truck-no ?no&:(not (member ?no $?ch))) (available-space ?sp) (last-run ?l))
	?t-rep<-(truck-report (truck-number ?no) (total-wait-time ?twt) (time-on-road ?tor) (percent-busy-time ?pb) (packages-transported ?pt) (avg-%-of-space-occupied ?aso) (non-delivery-time ?ndt) (%-time-delivering ?ptd))
	=>
	(retract ?t ?t-rep)
	(assert (check $?ch ?no))
	(bind ?wait (- ?f ?l))
	(bind ?twt (+ ?twt ?wait))
	(bind ?pb (* (/ ?tor ?f) 100))
	(bind ?aso (* (/ ?aso (* ?sp ?pt)) 100))
	(bind ?ptd (* (/ ?ptd ?tor) 100))
	(assert (truck-report (truck-number ?no) (total-wait-time ?twt) (time-on-road ?tor) (percent-busy-time ?pb) (packages-transported ?pt) (avg-%-of-space-occupied ?aso) (non-delivery-time ?ndt) (%-time-delivering ?ptd)))
)	

(defrule print-tr-now
	(declare (salience -20))
	?s<-(start-cal true)
	=>
	(retract ?s)
	(assert (print-tr-now true))
	(assert (temp4 1))
)

(defrule print-truck-report
	?t4<-(temp4 ?t-no)	
	(print-tr-now true)
	(truck-report (truck-number ?t-no) (total-wait-time ?twt) (time-on-road ?tor) (percent-busy-time ?pb) (packages-transported ?pt) (avg-%-of-space-occupied ?aso) (non-delivery-time ?ndt) (%-time-delivering ?ptd))
	=>
	(retract ?t4)
	(assert (temp4 =(+ ?t-no 1)))
	(open "s-table.txt" sim "a")
	(printout sim " "?t-no "		" ?twt "	   	" ?tor "            	  "  (integer ?pb) "	         	   " ?pt "	              " (integer ?aso) "	              	" ?ndt "	             " (integer ?ptd) crlf)
	(close sim)
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;handle time events- for future implementation ;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defrule entry-time
	(declare (salience -50))
?t2 <- (temp2 ?t&: (<= ?t 20))
(package (number ?n1&:(= ?n1 ?t))
			(arrival-time ?at)
			(expected-delivery-time ?e))
?et <- (event $?e1)
;(not (and (member$ ?at (create$ $?evt))(member$ ?e (create$ $?evt)))) trying to remove duplicates
=>
(retract ?t2 ?et)
(assert (event $?e1 ?at ?e))
(assert (temp2 =(+ ?t 1)))
)