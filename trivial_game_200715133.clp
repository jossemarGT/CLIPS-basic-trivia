;;;=====================================================================
;;;						Sistema experto de identificación de personajes
;;;		 				 200715133 - Jonnatan Jossemar Cordero Ramirez
;;;
;;;		Usualmente desarrollo / comento el código en ingles, pero en 
;;;		vista de que los inputs y outputs de este sistema experto están
;;;   en español, los comentarios estarán en el mismo lenguaje.
;;;
;;;		Parte de la lógica de este sistema experto deriva de "animal.clp"
;;;		incluido en los ejemplos para CLIPS 6.24
;;;		http://sourceforge.net/projects/clipsrules/files/CLIPS/6.24/examples_624.zip/download
;;;
;;;		Este proyecto es un ejemplo de "backward chaining rules", es el 
;;;		tipo de inferencia contrario al que implemente CLIPS, las cuales 
;;;		se encuentran en trivial_knowledgebase_200715133.clp y su definición 
;;;		se encuentra bajo el nombre de "rules", las cuales en base al 
;;;		objetivo actual determina la siguiente pregunta a realizar, una vez 
;;;		satisfecho el objetivo se descartan las reglas que ya no son 
;;;		necesarias y todos los personajes que no hacen match.
;;;
;;; 	La definción del template de personaje se encuentra como "character"
;;;		los hechos para este template se encuentran en trivial_characters_200715133.clp
;;;
;;;		Dado que el sistema experto debe permitir un rango de incerteza las
;;;		respuestas permitidas son si, no, no se, posiblemente si y
;;;		posiblemente no, las cuales dan una ponderación a los personajes
;;;		al final de la ronda de preguntas se elige al personaje restante
;;;		con mayor ponderación.
;;;		
;;;		Para ejecutar es necesario hacer load de este archivo, reset y run.
;;;=====================================================================

;;;***************************
;;;* DEFTEMPLATE DEFINITIONS *
;;;***************************

(deftemplate rule "Backward Chaining rules definition"
   (multislot if)
   (multislot then)
)

(deftemplate character "Character and its characteristics"
   (slot name (type STRING)(default ?NONE))
   (multislot properties)
   (slot certainty (type INTEGER)(default 0))
   ;+10 si
   ;+ 5 probablemente si
   ;- 5 probablemente no
   ; 0	no se (remueve regla)
   ; 0	no (remueve regla y personajes que no aplican)
)

(deftemplate legalanswer "Respuestas aceptadas"
		(multislot answers (type STRING))
)
   
;;;***************************
;;;*  DEFGLOBAL DEFINITIONS  *
;;;***************************
   
(defglobal 
		?*question-counter* = 1
		?*round-counter* = 1
		?*initialized* = 0
		?*current-possible-choice* = nil
		?*current-certainty-choice* = nil
		?*current-max-certainty* = 0
)

;;;**************************
;;;    UTILITY FUNCTIONS    
;;;**************************

(deffunction symbol2string (?symbol)
		(bind ?tmpstr (str-cat ?symbol))
		(bind ?tmp (str-index "." ?tmpstr))
		(while ?tmp
			(bind ?tmpstr ( str-cat (sub-string 1 (- ?tmp 1) ?tmpstr) " " (sub-string (+ ?tmp 1) (str-length ?tmpstr) ?tmpstr) ) )
			(bind ?tmp (str-index "." ?tmpstr))
		)
		(return ?tmpstr)
)

(deffunction string2symbol (?string)
		(bind ?tmpstr ?string)
		(bind ?tmp (str-index " " ?tmpstr))
		(while ?tmp
			(bind ?tmpstr ( str-cat (sub-string 1 (- ?tmp 1) ?tmpstr) "." (sub-string (+ ?tmp 1) (str-length ?tmpstr) ?tmpstr) ) )
			(bind ?tmp (str-index " " ?tmpstr))
		)
		(return (sym-cat ?tmpstr) )
)
   
;;;**************************
;;;* INFERENCE ENGINE RULES *
;;;**************************

(defrule assert-new-rules "Para cuando se quede sin preguntas, validando no repetir objetivos satisfechos"
		(declare (salience 30))
    (variable ?variable ?value) ; Dado los objetivos satisfechos
		(not (rule (if $?)(then $?)) ) ;Y no hay reglas en stack
		(character (name ?nombre) (properties ?ngoal ?nvalue $? )) ; Y hay todavía personajes
		(test (neq ?variable ?ngoal)) ; y la propiedad del personaje no es la misma que el objetivo satisfecho
		=>
		(bind ?*current-possible-choice* ?nombre)
		(assert (rule (if ?ngoal is si)
			(then ?ngoal is ?nvalue)) )
		(assert (goal is ?ngoal))
		(assert (question ?nvalue ?ngoal is (str-cat "¿ " (symbol2string ?ngoal) " " (symbol2string ?nvalue) " ?")) )		
		;(printout t "POST-INIT: Escribo regla (" ?ngoal ")" crlf)
		
)

(defrule assert-new-rules-init "Para cuando se quede sin preguntas y no hayan objetivos satisfechos"
		(declare (salience 30))
		(not (rule (if $?)(then $?)) ) ; No hay reglas
    (not (variable $?)) ; No hay objetivos satisfechos
		(character (name ?nombre) (properties ?ngoal ?nvalue $? )) ; Existen personajes en stack
		=>
		;Crear reglas
		(assert (rule (if ?ngoal is si)
			(then ?ngoal is ?nvalue)) )
		(assert (goal is ?ngoal))
		(assert (question ?nvalue ?ngoal is (str-cat "¿ " (symbol2string ?ngoal) " " (symbol2string ?nvalue) " ?")) )	
		
		;(printout t "INIT: Escribo regla (" ?ngoal ")" crlf)
)

(defrule goal-satified "Corrobora si se ha satisfecho el primer objetivo (final)"
		(declare (salience 50))
		?f <- (goal is ?goal)
		(variable ?goal ?value)
		(test (eq ?goal el.personaje.es))
		;(answer ? ?text ?goal)
		=>
		(retract ?f)
		(format t "%s : %s%n" (symbol2string ?goal) (symbol2string ?value))		
		(halt)
)

(defrule remove-old-rule "Quita las reglas que no hacen match o las que cuyos objetivos ya fueron satisfechos"
   (declare (salience 35))
   (variable ?variable ?)
   ?f <- (rule (if ?variable $?)(then ?variable $?)) 
   =>
   ;(printout t "Quitaré la regla con (" ?variable ")" crlf)
   (retract ?f)
)
   
(defrule remove-character-no-match-yes "Quita los personajes que no hacen match con los objetivos satisfechos"
   (declare (salience 35))
   (variable ?variable ?value)
   ?f <- (character (name ?nombre)(properties $? ?variable ~?value $?))
   =>
   (printout t "¡Adios! " ?nombre crlf)
   (retract ?f)
)

(defrule remove-character-no-match-no "Quita los personajes que no hacen match con los objetivos satisfechos"
   (declare (salience 35))
   (useranswer ?metavalue ?variable ?value)
   (test (eq ?value no))
   ?f <- (character (name ?nombre)(properties $? ?variable ?metavalue $?))
   =>
   (printout t "Adios >> " ?nombre crlf)
   (retract ?f)
)

(defrule modify-character-match "Modifica los personajes que si fueron elegidos"
   (declare (salience 40))
   (variable ?variable ?value)
   ?f <- (character (name ?nombre)(properties $?init ?variable ?value ? $?rest)(certainty ?cert))
   =>
   (bind ?cert (+ ?cert 10))
   (if (> ?cert ?*current-max-certainty* )
			then
			(bind ?*current-max-certainty* ?cert)
			(bind ?*current-certainty-choice* ?nombre)		
   )
   (modify ?f (name ?nombre)(properties ?init ?rest)(certainty ?cert))
   ;(printout t "Modificaré a " ?nombre " con certeza de: " ?cert crlf)
)

(defrule rule-satisfied-yes "Corrobora si la regla definida es satisfecha"
   (declare (salience 20))
   ?u <- (useranswer ?metavalue ?variable ?value)
   ?f <- (rule (if ?variable ? ?value)
               (then ?goal ? ?metavalue))
   =>
   (retract ?f)
   (assert (variable ?goal ?metavalue))
)

(defrule rule-satisfied-no "Corrobora si la regla fue negada por ende hay que cambiar de objetivo"
   (declare (salience 37))
   ?u <- (useranswer ?metavalue ?variable ?value)   
   (test (eq no ?value))
   ?f <- (rule (if ?variable $?)(then ?variable ? ?metavalue))
   ?c <- (character (name ?nombre)(properties $? ?variable ?metavalue $? ))
   =>
   (printout t "Adios " ?nombre crlf)
   (retract ?c)
   (retract ?f)
)

(defrule rule-partial-answer "A diferencia de 'rule-satisfied' esta maneja los valores probablemente.si probablemente.no"
   (declare (salience 50))
   (partialanswer $?answers)
   ?u <- (useranswer ?metavalue ?variable ?value)
   (test (member ?value ?answers ))
   ?f <- (rule (if ?variable $?)(then ?variable ? ?metavalue))
   =>
   ;(printout t "Quito regla (" ?variable ")" crlf)
   (retract ?f)
)


(defrule modify-character-partial-answer "A diferencia de 'rule-satisfied' esta maneja los valores probablemente.si probablemente.no"
   (declare (salience 40))
   (partialanswer ? $?answers)
   (partialyes ? $?y)
   (partialno ? $?n)
   (nullanswer ? $?nanswers)
   ?u <- (useranswer ?metavalue ?variable ?value)
   (test (member ?value ?answers ))
   ?f <- (character (name ?nombre)(properties $?init ?variable ?metavalue ? $?rest)(certainty ?cert))
   =>
   (if (member ?value  ?y)
			then
			(bind ?cert (+ ?cert 5))
   )
   (if (member ?value  ?n)
			then
			(bind ?cert (- ?cert 5))
   )
   ; Null does... nothing
   
   (if (> ?cert ?*current-max-certainty* )
			then
			(bind ?*current-max-certainty* ?cert)
			(bind ?*current-certainty-choice* ?nombre)		
   )
   
   (modify ?f (name ?nombre)(properties ?init ?rest)(certainty ?cert))
   (printout t "Modifico a " ?nombre " con certeza de " ?cert crlf)
)

(defrule ask-question-no-legalvalues "Para preguntas que su respuesta no son 'legalanswers' "
   (declare (salience 25))
   (not (legalanswer (answers $? )) )
   ?f1 <- (goal is ?variable)
   ?f2 <- (question ?value ?variable ? ?text)
   =>
   (retract ?f1 ?f2)
   (format t "%d.- %s" ?*question-counter* ?text)
   (assert (useranswer ?value ?variable (readline)))
)

(defrule ask-question-legalvalues "Preguntas que su respuestas son 'legalanswers' "
   (declare (salience 25))
   (legalanswer (answers $?answers) )
   ?f1 <- (goal is ?variable)
   ?f2 <- (question ?value ?variable ? ?text)
   =>
   (retract ?f1)
   (format t " %d.- %s " ?*question-counter* ?text)   
   (bind ?reply (lowcase(readline)))
   
   ;(printout t " >> "?reply crlf)
   
   (if (member ?reply ?answers) 
     then
				(bind ?tmp (str-index " " ?reply))
				(assert (useranswer ?value ?variable (string2symbol ?reply) ))
        (retract ?f2)
        (bind ?*question-counter* (+ ?*question-counter* 1)) ; Aumenta conteo de preguntas
     else
				(printout t " Las respuestas que se puede ingresar son " ?answers crlf crlf)
				(assert (goal is ?variable))
		)
)
     
(defrule check-question-limit-round-1 "Revisa si ya se alcanzó el máximo de preguntas por ronda"
		(declare (salience 100))
		(test (eq 15 ?*question-counter*))
		(test (eq 1 ?*round-counter*))
		=>		
		(printout t "Esta ha sido la primer ronda, permitame determinar su personaje..." crlf)
		(format t "¿Su personaje es %s?%n" ?*current-certainty-choice*)
		(bind ?*question-counter* 1)
		(bind ?*round-counter* 2)
		;Determinar personaje salir o seguir
)

(defrule check-question-limit-round-2 "Revisa si ya se alcanzó el máximo de preguntas por ronda"
		(declare (salience 100))
		(test (= 20 ?*question-counter*))
		(test (= 2 ?*round-counter*))
		=>
		(printout t "Esta ha sido la última ronda, permitame determinar su personaje..." crlf)
		(format t "¿Su personaje es %s?%n" ?*current-certainty-choice*)
		(bind ?*question-counter* 0)
		(bind ?*round-counter* 0)
)

(defrule init "Despliega instrucciones y carga todos los hechos (reglas y personajes)"
		(test (eq ?*initialized* 0))
		=>
		(bind ?*initialized* 1)
		(format t "%n======== Bienvenido al sistema experto de personajes =========%n%n" )
		(printout t "Piense en uno de los personajes descritos en la tabla de ayuda" crlf)
		(printout t "y permita que el sistema experto indage cual es el personaje, " crlf)
		(printout t "el sistema hará una serie de preguntas para ello, las únicas  " crlf)
		(printout t "respustas válidas son: si, no, no se, probablemente si y      " crlf)
		(format t "probablemente no.%n")
		(format t "Para iniciar presione ENTER%n")
		(readline)
		(format t "%n[Cargando personajes]")
		(load-facts trivial_characters_200715133.clp)
		
		(format t "[Preparando preguntas]%n%n")
		(dribble-on last-log.txt)
		(load-facts trivial_knowledgebase_200715133.clp)
		;Esto disparará ask-question-legalvalues
)
