theory collinear5
	imports Axioms Definitions Theorems
begin

theorem collinear5:
	assumes: `axioms`
		"A \<noteq> B"
		"col A B C"
		"col A B D"
		"col A B E"
	shows: "col C D E"
proof -
	have "col B C D" using collinear4[OF `axioms` `col A B C` `col A B D` `A \<noteq> B`] .
	have "col B C E" using collinear4[OF `axioms` `col A B C` `col A B E` `A \<noteq> B`] .
	consider "B \<noteq> C"|"B = C" by blast
	hence col C D E
	proof (cases)
		case 1
		have "col C D E" using collinear4[OF `axioms` `col B C D` `col B C E` `B \<noteq> C`] .
	next
		case 2
		have "col B D E" using collinear4[OF `axioms` `col A B D` `col A B E` `A \<noteq> B`] .
		have "col C D E" sorry
	next
	thus ?thesis by blast
qed

end