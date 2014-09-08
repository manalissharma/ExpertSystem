(defrule pre-start
	?init<-(initial-fact)
	=>
	(retract ?init)
	(assert (start-shortest false))
	(assert (start-delivering false))
	;(assert (now-you-can-remove-path1 false))
	;(assert (now-you-can-remove-path2 false))
)

(defrule begin
	?s<-(start-delivering true)
	=>
	(retract ?s)
	(assert (temp2 1)) ;to control entry of time in event fact
	(assert (event 1)) ;to control order of occurrence 
	(assert (current-time 0))
	;(assert (origin "Orlando"))
	(assert (package-checked))
	(assert (truck-checked))
	(assert (order-available 0)) 
	(assert (closest-truck 100))
	(assert (truck-route))
	(assert (time-now true))
	(assert (watch 0)) ;will store all time increments
	(assert (report-generation false))
	(assert (no-more dont-check))
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
;;;;;;;;;;;;;;;;find nearest truck;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule find-nearest-truck
	;(declare (salience 1))
	;(current-time ?x) ;no use here till now
	(order-available ?no&:(> ?no 0))
	(package (number ?no)  
			(depart-city ?dep-city) 
			(delivery-city ?del-city) 
			(size ?sz) 
			(arrival-time ?x))
	?tr-check <- (truck-checked $?assigned)
	?tr <- (truck (truck-no ?num&:(not (member ?num $?assigned)))
					(current-city ?cur-city)
					(destination ?dest) 
					(available-space ?space&:(>= ?space ?sz)) 
					(current-action "idle") 
					(current-time ?ct) 
					(occupied-space ?oc)
					(last-run ?last)
					)
	?close <- (closest-truck ?close-tr)
	(cheapest-route (all-stops ?dep-city $?hops ?cur-city) (lowest-cost ?lc&: (< ?lc ?close-tr)))
	;?nm <- (no-more check)
	=>
	(retract ?tr ?close ?tr-check)
	;(assert (no-more dont-check))
	(assert (truck (truck-no ?num)
					(current-city ?cur-city)
					(destination ?dest) 
					(available-space ?space) 
					(current-action "idle") 
					(current-time ?ct) 
					(occupied-space ?oc)
					(last-run ?last)
					))
	(assert (closest-truck ?lc))
	(assert (truck-checked $?assigned ?num)) 	
	)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;assign package to truck;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule pickup-after-waiting
	(declare (salience -2))
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
	?close <-(closest-truck ?)
	(test (< (- ?last ?at) 0))
	=>
	(retract ?order ?tr ?t-report ?p-report ?p-in ?close)
	(assert (closest-truck 100)) 
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
	
	;(assert (find-distance))
	(assert (current-time ?at))
	;(assert (event $?evt))
	(assert (order-available 0))
)

(defrule pickup-without-waiting
	(declare (salience -2))
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
	?close <-(closest-truck ?)
	(test (>= (- ?last ?at) 0))
	=>
	(retract ?order ?tr ?t-report ?p-report ?p-in ?close) 
	(assert (closest-truck 100))
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
	
	;(assert (find-distance))
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
	;?ro <-(cheapest-route (start ?cur-city) (stop ?dep-city) (lowest-cost ?c&:(>= ?c 0)))
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

	(cheapest-route (all-stops ?cur-city $?other ?dep-city) (lowest-cost ?lc))
	=>
	(retract ?tr ?t-report ?p-report)
	(bind ?pn (str-cat "for" ?no))
	(bind ?arr-time (+ ?at ?wt))
	(bind ?arr-time2 (+ ?arr-time ?lc))
	(bind ?actual-wait (+ ?wt ?lc))
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
	
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;deliver package to its destination;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule deliver
	;(origin ?or)
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
	;?ro <-(cheapest-route (start ?dep-city) (stop ?del-city) (lowest-cost ?c&:(>= ?c 0)))
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

	(cheapest-route (all-stops ?dep-city $?other ?del-city) (lowest-cost ?lc))
	=>
	(retract ?tr ?t-report ?p-report)
	(bind ?a-time (+ ?ct ?lc))
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
					(destination ?del-city) 
					(available-space ?space)
					(current-action "delivered") 
					(current-time ?a-time)  
					(package-carried ?no)
					))	
	
)

(defrule change-to-idle
	;(origin ?or)
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
					(current-action "delivered") 
					(current-time ?ct)  
					(package-carried ?no)
					(last-run ?last))
	(cheapest-route (all-stops ?del-city $?other ?del-city) (lowest-cost ?lc))
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
	(retract ?tr ?t-report)
	(bind ?a-time (+ ?ct ?lc))
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
						(action "idle") 
						(location ?del-city) 
						(arrival-time ?a-time)))
	(assert	(truck (truck-no ?num) 
					(current-city ?del-city) 
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
;;;;;;calculate all shortest paths;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	

(defrule connected-cities
	"calculate connected cities"
	(start-calculating-cheapest-routes true)
	?check<-(checked-city (for ?x) (checked $?ch))
	(distance (from ?x) (to ?y&:(not (member ?y $?ch))))
	?connect<-(connected-to (city ?x) (cities $?others))
	=>
	(retract ?check ?connect)
	(assert (connected-to (city ?x) (cities $?others ?y)))
	(assert (checked-city (for ?x) (checked $?ch ?y)))
)

(defrule start-shortest-for-all
	(declare (salience -10))
	?s<-(start-shortest false)
	=>
	(retract ?s)
	(assert (start-shortest true))
	(assert (next false))
)

(defrule start-calculate-shortest 
	?s<-(start-shortest true)
	(calculate-shortest-for ?x $?others)
	?all<-(all-city ?y $?rest)	
	=>
	(retract ?all ?s)
	(assert (shortest-distance1 (start ?x) (stop ?y) (shortest-dist -1)))
	(assert (all-city $?rest))
)

(defrule next-change
	(declare (salience -10))
	?n<-(next false)
	=>
	(retract ?n)
	(assert (next true))
)

(defrule next-calculate-shortest
	?n<-(next true)
	?cal<-(calculate-shortest-for ?x $?others)
	?all<-(all-city)	
	=>
	(retract ?n ?all ?cal)
	(assert (all-city "Tallahassee" "Lake City" "Orlando" "Ocala" "Jacksonville" "Gainesville" 
							"St. Augustine" "West Palm" "Tampa" "Ft. Myers" "Miami" "Key West"))
	(assert (calculate-shortest-for $?others))
	(assert (next false))
)

(defrule initial-route 
	(declare (salience 2)) 
	(shortest-distance1 (start ?x)) 
	;(find-distance)
	=> 
	(assert (route (nodes ?x) (cost 0)))
)
 
(defrule extended-route 
	(declare (salience 2)) 
	;(find-distance)
	(route (nodes $?n ?y) (cost ?w)) 
	(distance (from ?y) (to ?z & ~?y & :(not (member ?z $?n))) (cost ?we)) 
	=> 
	(assert (route (nodes $?n ?y ?z) (cost (+ ?w ?we))))
) 
 
(defrule prune-not-required-route 
	(declare (salience 10))
	;(find-distance) 
	(route (nodes $? ?x) (cost ?w1)) 
	?route <- (route (nodes $? ?x) (cost ?w2&:(> ?w2 ?w1))) 
	=> 
	(retract ?route)
) 
 
(defrule cal-cheapest-route
 	(declare (salience 1)) 
	;?f<-(find-distance)
 	?s<-(shortest-distance1 (start ?x) (stop ?y)) 
 	?route <-(route (nodes $?n ?y) (cost ?w)) 
 	;?now1 <- (now-you-can-remove-path1 false)
	 => 
	(retract ?s ?route)
	(assert (cheapest-route (all-stops ?x $?n ?y) (lowest-cost ?w)))
	(assert (start-shortest true))
	;(assert (now-you-can-remove-path1))
	;(assert (low-cost-routes ?route))
)

(defrule remove-duplicate-source
	(declare (salience 1))
	?cp <- (cheapest-route (all-stops ?a ?b&: (eq ?b ?a) $?c ?d) (lowest-cost ?w))
	=>
	(retract ?cp)
	(assert (cheapest-route (all-stops ?a $?c ?d) (lowest-cost ?w)))
)

(defrule remove-path
	(declare (salience 1))
	?r <-(route)
	;?now1 <- (now-you-can-remove-path1)
	=>
	(retract ?r)
				
)

(defrule start-delivering-packages
	(declare (salience -20))
	?s1<-(start-shortest true)
	?s2<-(start-delivering false)
	?n<-(next true)
	=>
	(retract ?n ?s1 ?s2)
	(assert (start-delivering true))	
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
	(printout sim "Report Generated:" crlf " Time		Package No.		Truck No.		Action		     Location		       Arrival Time " crlf)
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
			(printout sim "  "?time1 "	    	" ?p-no "			" ?t-no "			" ?act "	" ?city "		" ?a-time crlf)
			else
			(printout sim "  "?time1 "		    " ?p-no "			" ?t-no "			" ?act "	" ?city "		" ?a-time crlf)
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
	(printout sim ""?avg-wt "	" ?pdot "			   " ?pdl "				      " ?avg-l "		         	" ?avg-l-all  crlf)
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

