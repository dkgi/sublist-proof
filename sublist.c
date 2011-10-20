/**
  * Sublist.c contains the functions and proofs to get a maximum
  * common sublist of two list of chars.
  * 
  * Author: Dominik Gabi (dgabi[(ta)^-1]student.ethz.ch)
  *
  * The following code and proof extends the iter.c example
  * which is available at: 
  * http://people.cs.kuleuven.be/~bart.jacobs/verifast/examples/
  *
  * The code has been successfully verified in Verifast 10.4 IDE.
  * Please note that I have not included tests to prevent arithmeitc
  * overflow. In order to verify, you have to disable the checks.
  *
  * The comments in this file are not meant to be comprehensive.
  * For more details on the architecture and a few of the more
  * complicated proofs, please consult the accompanying report.
  **/

#include "stdlib.h"

/**
  * Basic data structures. Node defines a single node in a linked
  * list and list a wrapper containing the first node and the node
  * after the last one.
  **/

struct node {
	struct node *next;
	char value;
};

/*@

predicate node(struct node *node; struct node *next, char value)
	requires malloc_block_node(node) &*& node->next |-> next &*& node->value |-> value;

predicate segment(struct node *first, struct node *last; list<char> values)
	requires first == last ? values == nil
		: node(first, ?next, ?value) &*& segment(next, last, ?tail) &*& values == cons(value, tail);

@*/

struct list {
	struct node *first;
	struct node *after;
};

/*@

predicate list(struct list *list; list<char> values)
	requires malloc_block_list(list) &*& list->first |-> ?first &*& list->after |-> ?after
		&*& segment(first, after, values) &*& node(after, _, _);

@*/


/**
  * Basic operations follow for creating and disposing lists.
  **/

struct list *list_create()
	//@ requires true;
	//@ ensures list(result, nil);
{
	struct list *result = malloc(sizeof(struct list));
	if (result == 0) abort();
	struct node *after = malloc(sizeof(struct node));
	if (after == 0) abort();
	after->next = 0;
	
	result->first = after;
	result->after = after;

	return result;
}

void list_dispose(struct list *list)
	//@ requires list(list, _);
	//@ ensures true;
{
	struct node *this = list->first;
	struct node *after = list->after;
	
	while (this != after)
		//@ invariant segment(this, after, _);
	{
		//@ open node(this, _, _);
		struct node *next = this->next;
		free(this);
		this = next;
	}
	
	free(after);
	free(list);
}

/**
  * Segments represent partail lists. Their purpose is to be 
  * able to iterate over lists. For example if we divide the
  * list with an iterator we can express that half the list
  * is on the left, and the other half on the right side of
  * the iterator.
  *
  * The lemmas defined also proof what happens when we append/
  * prepend a single element or a whole segment to a segment.
  * These are used to move from one iteration to another.
  **/

/*@

lemma void distinct_nodes(struct node *n1, struct node *n2)
	requires node(n1, ?nn1, ?v1) &*& node(n2, ?nn2, ?v2);
	ensures node(n1, nn1, v1) &*& node(n2, nn2, v2) &*& n1 != n2;
{
	open node(n1, _, _);
	open node(n2, _, _);
	close node(n1, _, _);
	close node(n2, _, _);
}

lemma void segment_add(struct node *n2)
	requires segment(?n1, n2, ?values) &*& node(n2, ?n3, ?value) &*& node(n3, ?n4, ?v3);
	ensures segment(n1, n3, append(values, cons(value, nil))) &*& node(n3, n4, v3);
{
	distinct_nodes(n2, n3);
	open segment(n1, n2, values);
	if (n1 != n2) {
		distinct_nodes(n1, n3);
		segment_add(n2);
	}	
	close segment(n1, n3, append(values, cons(value, nil)));
}

lemma void segment_prepend(struct node *previous)
	requires node(previous, ?next, ?v) &*& segment(next, ?after, ?v1) &*& previous != after;
	ensures segment(previous, after, cons(v, v1));
{
	close segment(previous, after, cons(v, v1));
} 

lemma void segment_append(struct node *n1, struct node *n2, struct node *n3)
	requires segment(n1, n2, ?values1) &*& segment(n2, n3, ?values2) &*& node(n3, ?n4, ?v3);
	ensures segment(n1, n3, append(values1, values2)) &*& node(n3, n4, v3);
{
	open segment(n1, n2, values1);
	switch(values1) {
		case nil:
		case cons(value, rest):
			distinct_nodes(n1, n3);
			open segment(n2, n3, values2);
			segment_append(n1->next, n2, n3);
			close segment(n1, n3, append(values1, values2));
	}
}

predicate segment2(struct node *first, struct node *last, struct node *after, list<char> values)
 	requires
 		switch (values) {
 			case nil: return first == last;
 			case cons(head, tail):
 				return first != after &*& node(first, ?next, head) &*& segment2(next, last, after, tail);
 		};
 
lemma void segment2_add(struct node *first)
	requires segment2(first, ?last, ?after, ?values) &*& node(last, ?next, ?value) &*& last != after;
	ensures segment2(first, next, after, append(values, cons(value, nil)));
{
	open segment2(first, last, after, values);
	switch (values) {
		case nil:
			close segment2(next, next, after, nil);
		case cons(head, tail):
			open node(first, ?fnext, head);
			segment2_add(fnext);
			close node(first, fnext, head);
	}
	close segment2(first, next, after, append(values, cons(value, nil)));
}

lemma void segment2_to_segment(struct node *first)
	requires segment2(first, ?last, ?after, ?values) &*& last == after;
	ensures segment(first, last, values);
{
	switch (values) {
		case nil:
			open segment2(first, last, after, values);
			close segment(first, last, values);
		case cons(head, tail):
			open segment2(first, last, after, values);
			open node(first, ?next, head);
			segment2_to_segment(next);
			close node(first, next, head);
			close segment(first, last, values);
	}
}

@*/

/**
  * We continue with basic list operations for adding/removing 
  * elements, copying the list, getting the length of the list etc. 
  **/

void list_add(struct list *list, char value)
	//@ requires list(list, ?values);
	//@ ensures list(list, append(values, cons(value, nil)));
{
	struct node *after = malloc(sizeof(struct node));
	if (after == 0) abort();
	after->next = 0;
	
	struct node *node = list->after;
	node->value = value;
	node->next = after;
	list->after = after;
	//@ segment_add(node);
}

void list_append(struct list *list1, struct list *list2)
	//@ requires list(list1, ?values1) &*& list(list2, ?values2);
	//@ ensures list(list1, append(values1, values2));
{
	struct node *a1 = list1->after;
	struct node *f2 = list2->first;
	struct node *a2 = list2->after;
	
	//@ open segment(f2, a2, values2);
	if (f2 == a2) {
		free(f2);
		free(list2);
		//@ append_nil(values2);
	} else {
		a1->next = f2->next;
		a1->value = f2->value;
		list1->after = a2;
		free(f2);
		free(list2);
		//@ distinct_nodes(a1, a2);
		//@ close segment(a1, a2, values2);
		//@ segment_append(list1->first, a1, a2);
		//@ close list(list1, append(values1, values2));
	}
}

int list_length(struct list *list)
	//@ requires list(list, ?values);
	//@ ensures list(list, values) &*& result == length(values);
{
	//@ open list(list, values);
	struct node *first = list->first;
	struct node *after = list->after;
	struct node *this = list->first;
	int result = 0;
	//@ close segment2(first, first, after, nil);
	while (this != after)
		//@ invariant segment2(first, this, after, ?v1) &*& segment(this, after, ?v2) &*& values == append(v1, v2) &*& result == length(v1);
	{
		//@ open segment(this, after, v2);
		//@ open node(this, _, ?value);
		struct node *next = this->next;
		//@ close node(this, next, _);
		//@ segment2_add(first);
		this = next;
		result++;
		//@ assert segment(next, after, ?v3);
		//@ append_assoc(v1, cons(value, nil), v3); 
	}
	
	//@ open segment(this, after, v2);
	//@ append_nil(v2);
	//@ segment2_to_segment(first);
	//@ close list(list, values);
	return result;
}

struct list *list_copy(struct list *list)
	//@ requires list(list, ?values);
	//@ ensures list(list, values) &*& list(result, values);
{
	//@ open list(list, values);
	struct list *result = list_create();
	struct node *first = list->first;
	struct node *this = first;
	struct node *after = list->after;
	//@ close segment2(first, first, after, nil);
	while (this != after)
		//@ invariant segment2(first, this, after, ?v1) &*& segment(this, after, ?v2) &*& values == append(v1, v2) &*& list(result, v1);
	{
		//@ open segment(this, after, v2);
		//@ open node(this, _, ?value);
		struct node *next = this->next;
		list_add(result, this->value);
		//@ close node(this, next, _);
		//@ segment2_add(first);
		this = next;
		//@ assert segment(next, after, ?v3);
		//@ append_assoc(v1, cons(value, nil), v3);
	}
	//@ open segment(this, after, v2);
	//@ append_nil(v2);
	//@ segment2_to_segment(first);
	//@ close list(list, values);
	return result;
}

char list_drop_one(struct list *list)
	//@ requires list(list, ?values) &*& 0 < length(values);
	//@ ensures list(list, ?tail) &*& tail == drop(1, values);
{
	//@ open list(list, values);
	struct node *first = list->first;
	//@ open segment(first, ?after, values);
	char result = first->value;
	struct node *next = first->next;
	list->first = next;
	free(first);
	return result;
}

void list_drop_n(struct list *list, int n)
	//@ requires list(list, ?values) &*& 0 <= n &*& n <= length(values);
	//@ ensures list(list, drop(n, values));
{
	int count = 0;
	while (count < n)
		//@ invariant list(list, ?dropped) &*& dropped == drop(count, values) &*& length(dropped) == length(values) - count &*& 0 <= count &*& count <= n;
	{
		char v = list_drop_one(list);
		//@ drop_n_plus_one(count, values);
		count++;
	}
}

void list_reverse(struct list *list)
	//@  requires list(list, ?values);
	//@  ensures list(list, reverse(values));
{
	struct node *first = list->first;
	struct node *after = list->after;
	struct node *previous = after;
	struct node *this = first;
	
	while (this != after) 
		//@ invariant segment(previous, after, ?v1) &*& segment(this, after, ?v2) &*& values == append(reverse(v1), v2);
	{
		//@ open segment(this, after, v2);
		//@ open node(this, _, ?v);
		struct node *next = this->next;
		this->next = previous;
		previous = this;
		//@ close segment(previous, after, cons(v, v1));
		this = next;
		//@ assert segment(this, after, tail(v2));
		//@ assert segment(previous, after, cons(v, v1));
		//@ append_assoc(reverse(v1), cons(v, nil), tail(v2));
		//@ assert values == append(reverse(cons(v, v1)), tail(v2));
	}
	
	list->first = previous;
	//@ assert this == after;
	//@ open segment(this, after, v2);
	//@ assert list(list, reverse(values));
}

/**
  * The following lemmas make statements about reverse lists 
  * and how the drop and take functions interact with reversed
  * lists.
  **/

/*@

lemma void reverse_length<t>(list<t> list)
	requires true;
	ensures length(list) == length(reverse(list));
{
	switch (list) {
		case nil:			// length(nil) == length(nil)
		case cons(x, xs):
			reverse_length(xs);
	}
}

lemma void drop_append<t>(list<t> x1, list<t> x2, int n)
	requires 0 <= n &*& n <= length(x1);
	ensures drop(n, append(x1, x2)) == append(drop(n, x1), x2);
{
	switch (x1) {
		case nil:
		case cons(head, tail):
			if (n == 0) {
				drop_0(append(x1, x2));
			} else {
				drop_append(tail, x2, n-1);
			}
		
	}
}

lemma void reverse_drop_tail<t>(t x, list<t> xs, int n)
	requires 0 <= n &*& n <= length(xs);
	ensures reverse(drop(n, reverse(cons(x, xs)))) == cons(x, reverse(drop(n, reverse(xs))));
{
	assert reverse(cons(x, xs)) == append(reverse(xs), cons(x, nil));
	reverse_length(xs);
	drop_append(reverse(xs), cons(x, nil), n);
	assert drop(n, append(reverse(xs), cons(x, nil))) == append(drop(n, reverse(xs)), cons(x, nil));
	reverse_append(drop(n, reverse(xs)), cons(x, nil));
	assert append(cons(x, nil), reverse(drop(n, reverse(xs)))) == cons(x, reverse(drop(n, reverse(xs))));
	
}

lemma void reverse_drop_reverse<t>(list<t> list, int n)
	requires 0 <= n &*& n <= length(list);
	ensures reverse(drop(length(list)-n, reverse(list))) == take(n, list);
{
	switch (list) {
		case nil:
		case cons(head, tail):
			if (n == 0) {
				reverse_length(list);
			} else if (n == length(list)) {
			} else {
				reverse_drop_reverse(tail, n-1);
				assert take(n, cons(head, tail)) == cons(head, take(n-1, tail));
				assert length(list) - n == length(tail) - (n-1);
				reverse_drop_tail(head, tail, length(list) - n);
				assert reverse(drop(length(list)-n, reverse(list))) == cons(head, reverse(drop(length(tail)-(n-1), reverse(tail))));
			}
	}
}

@*/

void list_take_n(struct list *list, int n)
	//@ requires list(list, ?values) &*& 0 <= n &*& n <= length(values);
	//@ ensures list(list, take(n, values));
{
	//@ open list(list, values);
	list_reverse(list);
	//@ reverse_length(values);
	int drop = list_length(list);
	drop -= n;
	list_drop_n(list, drop);
	list_reverse(list);
	//@ reverse_drop_reverse(values, n);	
}

struct list *list_sublist(struct list *list, int i, int j)
	//@ requires list(list, ?values) &*& 0 <= i &*& i <= j &*& j <= length(values);
	//@ ensures list(list, values) &*& list(result, take(j-i, drop(i, values)));
{
	struct list *result = list_copy(list);
	list_drop_n(result, i);
	list_take_n(result, j - i);
	return result;
}

/**
  * Since it is hard to write inductive proofs with the == relation on
  * lists, I have introduced a recursive fixpoint function to
  * define equality of lists. The two auto lemmas are proof that
  * this fixpoint function indeed corresponds to ==.
  **/

/*@

fixpoint bool list_equals<t>(list<t> l1, list<t> l2) {
	switch (l1) {
		case nil: return l2 == nil;
		case cons(x, xs): return l2 != nil && x == head(l2) && list_equals(xs, tail(l2));
	}
}	

lemma_auto void list_equals_to_equals<t>(list<t> l1, list<t> l2)
	requires l1 == l2;
	ensures true == list_equals(l1, l2);
{
	switch (l1) {
		case nil:
			assert l2 == nil;
		case cons(x, xs):
			assert l2 != nil;
			assert head(l1) == head(l2);
			list_equals_to_equals(xs, tail(l2));
	}
}

lemma_auto void equals_to_list_equals<t>(list<t> l1, list<t> l2)
	requires true == list_equals(l1, l2);
	ensures l1 == l2;
{
	switch (l1) {
		case nil:
			assert l2 == nil;
		case cons(x1, xs1):
			switch (l2) {
				case nil:
					assert l2 == nil;
				case cons(x2, xs2):
					equals_to_list_equals(xs1, xs2);
			}
	}
}

lemma void list_equals_transitive<t>(list<t> l1, list<t> l2, list<t> l3)
	requires true == list_equals(l1, l2) &*&  true == list_equals(l2, l3);
	ensures true == list_equals(l1, l3);
{
}

@*/

/**
  * The length of a list can be used to argue about its properties.
  * The following lemmas are proofs of a few of those. For most of
  * the simpler proof it is sufficient to open a switch statement
  * to force verifast to make a case distinction.
  **/

/*@

lemma void list_length_not_equal<t>(list<t> l1, list<t> l2)
	requires length(l1) != length(l2);
	ensures false == list_equals(l1, l2);
{
	switch (l1) {
		case nil:
			assert l2 != nil;
		case cons(x1, xs1):
			switch (l2) {
				case nil:
					assert l2 == nil;
				case cons(x2, xs2):
					list_length_not_equal(xs1, xs2);
			}
	}
}

lemma void list_length_not_0<t>(list<t> list)
	requires list != nil;
	ensures length(list) > 0;
{
	switch (list) {
		case nil: 
		case cons(x, xs):
	}
}

lemma void list_length_nil<t>(list<t> list)
	requires length(list) == 0;
	ensures list == nil;
{
	switch (list) {
		case nil:
		case cons(x, xs):
	}
}

lemma void list_length_tail<t>(list<t> list, int l)
	requires length(list) == l &*& 0 < l;
	ensures length(tail(list)) == l-1;
{
	switch (list) {
		case nil:
		case cons(x, xs):
	}
}

lemma void list_add_not_equals<t>(list<t> l1, list<t> l2, t v1, t v2)
	requires v1 != v2;
	ensures false == list_equals(append(l1, cons(v1, nil)), append(l2, cons(v2, nil)));
{
	switch (l1) {
		case nil:
			switch (l2) {
				case nil:
				case cons(x2, xs2):
			}
		case cons(x1, xs1):
			switch (l2) {
				case nil:
					list_length_not_equal(append(l1, cons(v1, nil)), append(l2, cons(v2, nil)));
				case cons(x2, xs2):
					list_add_not_equals(xs1, xs2, v1, v2);
			}
	}
}

lemma void list_add_equals<t>(list<t> l1, list<t> l2, t v1, t v2, bool equals)
	requires list_equals(l1, l2) == equals &*& v1 == v2;
	ensures equals == list_equals(append(l1, cons(v1, nil)), append(l2, cons(v2, nil)));
{
	switch (l1) {
		case nil:
			switch (l2) {
				case nil:
				case cons(x2, xs2):
			}
		case cons(x1, xs1):
			switch (l2) {
				case nil:
					list_length_not_equal(append(l1, cons(v1, nil)), append(l2, cons(v2, nil)));
				case cons(x2, xs2):
					if (equals == true) {
						list_add_equals(xs1, xs2, v1, v2, true);
					} else {
						if (x1 == x2) {
							list_add_equals(xs1, xs2, v1, v2, equals);
						} else {
							assert false == list_equals(append(l1, cons(v1, nil)), append(l2, cons(v2, nil)));
						}
					}
			}
	}
}

lemma void list_segment_equal_nil(list<char> l1, list<char> l2, struct node *t1, struct node *a1, struct node *t2, struct node *a2) 
	requires segment(t1, a1, l1) &*& segment(t2, a2, l2) &*& length(l1) == length(l2) &*& (t1 == a1 || t2 == a2);
	ensures segment(t1, a1, l1) &*& segment(t2, a2, l1) &*& l1 == nil &*& l2 == nil;
{
	open segment(t1, a1, l1);
	open segment(t2, a2, l2);
	if (t1 == a1) {
		list_length_nil(l2);
		list_length_nil(l1);
	} else {
		list_length_nil(l1);
		list_length_nil(l2);
	}
}

/**
  * The newly defined list equality is then used in the
  * following function that compares two lists.
  **/

@*/

bool list_equal(struct list *list1, struct list *list2)
	//@ requires list(list1, ?values1) &*& list(list2, ?values2);
	//@ ensures list(list1, values1) &*& list(list2, values2) &*& result == list_equals(values1, values2);
{
	bool result = true;
	
	int l1 = list_length(list1);
	int l2 = list_length(list2);
	
	if (l1 != l2) {
		//@ list_length_not_equal(values1, values2);
		return false;
	}
	
	struct node *first1 = list1->first;
	struct node *first2 = list2->first;
	struct node *after1 = list1->after;
	struct node *after2 = list2->after;
	struct node *this1 = first1;
	struct node *this2 = first2;
	
	//@ close segment2(first1, this1, after1, nil);
	//@ close segment2(first2, this2, after2, nil);
	while (this1 != after1 && this2 != after2)
		//@ invariant segment2(first1, this1, after1, ?v11) &*& segment2(first2, this2, after2, ?v12) &*& segment(this1, after1, ?v21) &*& segment(this2, after2, ?v22) &*& values1 == append(v11, v21) &*& values2 == append(v12, v22) &*& length(v21) == length(v22) &*& result == list_equals(v11, v12);
	{
		//@ open segment(this1, after1, _);
		//@ open segment(this2, after2, _);
		//@ open node(this1, _, ?value1);
		//@ open node(this2, _, ?value2);
		struct node *next1 = this1->next;
		struct node *next2 = this2->next;
		if (this1->value == this2->value) {
			result = result && true;
			//@ list_add_equals(v11, v12, value1, value2, result);
		} else {
			result = false;
			//@ list_add_not_equals(v11, v12, value1, value2);
		}
		this1 = next1;
		this2 = next2;
		//@ segment2_add(first1);
		//@ segment2_add(first2);
		//@ assert segment(next1, after1, ?v31);
		//@ assert segment(next2, after2, ?v32);
		//@ append_assoc(v11, cons(value1, nil), v31);
		//@ append_assoc(v12, cons(value2, nil), v32);
	}

	//@ list_segment_equal_nil(v21, v22, this1, after1, this2, after2);
	
	//@ open segment(this1, after1, v21);
	//@ open segment(this2, after2, v22);
	//@ append_nil(v21);
	//@ append_nil(v22);
	//@ segment2_to_segment(first1);
	//@ segment2_to_segment(first2);
	//@ close list(list1, values1);
	//@ close list(list2, values2);
	return result;
}

/**
  * The following proofs state simple facts about the take/drop 
  * functions.
  **/

/*@

lemma void list_take_tail<t>(int n, list<t> l1, list<t> l2)
	requires l2 == tail(take(n, l1)) &*& n > 0;
	ensures l2 == take(n-1, tail(l1));
{
	switch (l1) {
		case nil: // does not happen
		case cons(x, xs):
	}
}

lemma void list_take_tail_reverse<t>(int n, list<t> l1, list<t> l2)
	requires l2 == take(n, tail(l1)) &*& 0 <= n;
	ensures l2 == tail(take(n+1, l1));
{
	switch (l1) {
		case nil:
		case cons(x, xs):
	}
}

lemma void list_take_head<t>(int n, list<t> list, t head)
	requires head(list) == head &*& 0 < length(list) &*& 0 < n;
	ensures head(take(n, list)) == head;
{
	switch (list) {
		case nil: assert false;
		case cons(x, xs):
	}
}

lemma void take_drop_one<t>(list<t> list, int length)
	requires length(list) == length &*& 0 < length;
	ensures take(length-1, drop(1, list)) == tail(list);
{
	switch (list) {
		case nil: assert false;
		case cons(x, xs):
	}
}
 
@*/

/**
  * The next predicates, functions and lemmas are about common
  * sublists.
  **/

/*@

predicate list_common_sublist<t>(list<t> sublist, int l, list<t> list1, list<t> list2)
	requires length(sublist) == l
		&*& true == list_equals(sublist, take(l, list1))
		&*& true == list_equals(sublist, take(l, list2));


fixpoint bool list_common_sublist<t>(list<t> sublist, int l, list<t> list1, list<t> list2) {
	switch (sublist) {
		case nil: return l == 0;
		case cons(x, xs): return x == head(list1) && x == head(list2) && list_common_sublist(xs, l-1, tail(list1), tail(list2)); 
	}
}

lemma void list_common_sublist_tail<t>(list<t> sublist, int l, list<t> list1, list<t> list2)
	requires list_common_sublist(sublist, l, list1, list2) &*& 0 < l;
	ensures list_common_sublist(tail(sublist), l-1, tail(list1), tail(list2)) &*& head(sublist) == head(take(l,list1)) &*& head(sublist) == head(take(l, list2));
{
	open list_common_sublist(sublist, l, list1, list2);
	list_length_tail(sublist, l);
	list_take_tail(l, list1, tail(sublist));
	list_take_tail(l, list2, tail(sublist));
	close list_common_sublist(tail(sublist), l-1, tail(list1), tail(list2));
}

lemma void list_common_sublist_not_equal<t>(list<t> sublist, int l, list<t> list1, list<t> list2)
	requires take(l, list1) != take(l, list2) &*& l == length(sublist) &*& l <= length(list1) &*& l <= length(list2);
	ensures false == list_common_sublist(sublist, l, list1, list2);
{	
	switch (sublist) {
		case nil:
			list_length_nil(list1);
			list_length_nil(list2);				// Contradiction (list1 == list2)
		case cons(z, zs):
			switch (list1) {
				case nil:				// Contradiction
				case cons(x, xs):
					switch (list2) {
						case nil: 		// Contradiction
						case cons(y, ys):
							if (x != y) {
								assert false == list_common_sublist(sublist, l, list1, list2);
							} else {
								list_common_sublist_not_equal(zs, l-1, xs, ys);
								assert false == list_common_sublist(sublist, l, list1, list2);
							}
					}
			}
	}
}

lemma void list_common_sublist_to_fixpoint<t>(list<t> sublist, int l, list<t> list1, list<t> list2)
	requires list_common_sublist(sublist, l, list1, list2) &*& l == length(sublist) &*& l <= length(list1) &*& l <= length(list2);
	ensures true == list_common_sublist(sublist, l, list1, list2);
{
	switch (sublist) {
		case nil: 
			open list_common_sublist(sublist, l, list1, list2);
			assert true == list_common_sublist(sublist, l, list1, list2);
		case cons(x, xs):
			list_length_not_0(cons(x, xs));
			list_common_sublist_tail(sublist, l, list1, list2);
			list_length_tail(list1, length(list1));
			list_length_tail(list2, length(list2));
			list_common_sublist_to_fixpoint(xs, l-1, tail(list1), tail(list2));
			
			list_take_head(l, list1, head(list1));
			list_take_head(l, list2, head(list2));
			
			assert true == list_common_sublist(sublist, l, list1, list2);		
	}
}

lemma void list_common_sublist_to_predicate<t>(list<t> sublist, int l, list<t> list1, list<t> list2)
	requires true == list_common_sublist(sublist, l , list1, list2) &*& l == length(sublist) &*& l <= length(list1) &*& l <= length(list2);
	ensures list_common_sublist(sublist, l, list1, list2);
{
	switch (sublist) {
		case nil:
			close list_common_sublist(sublist, l, list1, list2);
		case cons(x, xs):
			list_length_tail(list1, length(list1));
			list_length_tail(list2, length(list2));
			list_common_sublist_to_predicate(xs, l-1, tail(list1), tail(list2));
			open list_common_sublist(xs, l-1, tail(list1), tail(list2));
			
												// 1 (take(l, list1) != nil)
			list_take_head(l, list1, x);						// 2 (x == head(take(l, list1)))
			list_take_head(l, list2, x);
			list_equals_to_equals(xs, take(l-1, tail(list1)));			// 3 (take(l-1, tail(list1)) == tail(take(l, list1)))
			list_equals_to_equals(xs, take(l-1, tail(list2)));
			list_take_tail_reverse(l-1, list1, xs);		
			list_take_tail_reverse(l-1, list2, xs);
			
			assert true == list_equals(sublist, take(l, list1));
			assert true == list_equals(sublist, take(l, list2));
			close list_common_sublist(sublist, l, list1, list2);
	}	
}


predicate list_maximum_common_sublist_0<t>(list<t> sublist, list<t> list1, list<t> list2)
	requires true == list_common_sublist(sublist, length(sublist), list1, list2) 
		&*& (false == list_common_sublist(take(length(sublist)+1, list1), length(sublist)+1, list1, list2) 
		|| length(sublist) == length(list1)
		|| length(sublist) == length(list2));		

@*/

/**
  * The list_maximum_common_sublist_0 function returns the maximum
  * common sublist starting at position 0.
  **/

struct list *list_maximum_common_sublist_0(struct list *list1, struct list *list2)
	//@ requires list(list1, ?v1) &*& list(list2, ?v2);
	//@ ensures list(list1, v1) &*& list(list2, v2) &*& list(result, ?v3) &*& list_maximum_common_sublist_0(v3, v1, v2);
{
	struct list *result = list_create();
	
	int l1 = list_length(list1);
	int l2 = list_length(list2);
	int n = (l1 < l2) ? l1 : l2;
	
	int i = 1;
	bool abort = false;
	while (i <= n && !abort)
		/*@ 
		invariant list(list1, v1) &*& list(list2, v2) &*& list(result, ?v3) 
			&*& 0 <= i &*& i <= n+1
			&*& abort ? 
				true == list_common_sublist(v3, i-2, v1, v2) &*& length(v3) == i-2 &*& false == list_common_sublist(take(i-1, v1), i-1, v1, v2)
			: 
				true == list_common_sublist(v3, i-1, v1, v2) &*& length(v3) == i-1;
		@*/
	{
		struct list *sub1 = list_sublist(list1, 0, i);
		struct list *sub2 = list_sublist(list2, 0, i);
		bool equal = list_equal(sub1, sub2);
		
		if (equal) {
			list_dispose(result);
			result = list_copy(sub1);
			//@ assert list(result, ?r);
			//@ close list_common_sublist(r, i, v1, v2);
			//@ list_common_sublist_to_fixpoint(r, i, v1, v2);
			//@ assert !abort;
		} else {
			//@ assert list(sub1, ?s1) &*& list(sub2, ?s2);
			//@ list_common_sublist_not_equal(s1, i, v1, v2);
			//@ assert false == list_common_sublist(take(i, v1), i, v1, v2);
			abort = true;
		}
		
		list_dispose(sub1);
		list_dispose(sub2);
		
		i++;
	}
	

	//@ close list_maximum_common_sublist_0(v3, v1, v2);
	return result;
}

/**
  * The maximum common sublist predicate defines what a 
  * maximum common sublist is in a recursive manner.
  **/

/*@

predicate list_maximum_common_sublist<t>(list<t> sublist, list<t> list1, list<t> list2)
	requires list1 == nil || list2 == nil ?
			sublist == nil 
		:		
			list_maximum_common_sublist(?vl, tail(list1), list2) &*& list_maximum_common_sublist(?vr, list1, tail(list2)) 
			&*& list_maximum_common_sublist_0(?vm, list1, list2)
			&*& length(vm) >= length(vl) && length(vm) >= length(vr) ?
				sublist == vm
			:
				length(vl) >= length(vr) ? 
					sublist == vl
				:
					sublist == vr;

@*/

/**
  * And finally the list_maximum_common_sublist function.
  **/

struct list *list_maximum_common_sublist(struct list *list1, struct list *list2)
	//@ requires list(list1, ?v1) &*& list(list2, ?v2);
	//@ ensures list(list1, v1) &*& list(list2, v2) &*& list(result, ?v3) &*& list_maximum_common_sublist(v3, v1, v2);

{
	int l1 = list_length(list1);
	int l2 = list_length(list2);
	
	struct list *left = 0;
	struct list *middle = 0;
	struct list *right = 0;
	struct list *result = 0;
	
	int ll = 0;
	int lm = 0;
	int lr = 0;
	
	if (l1 == 0) {
		result = list_create();
		//@ list_length_nil(v1);
	} else if (l2 == 0) {
		result = list_create();
		//@ list_length_nil(v2);
	} else {
		struct list *tl = list_sublist(list1, 1, l1);
		left = list_maximum_common_sublist(tl, list2);
		ll = list_length(left);
		list_dispose(tl);
		//@ take_drop_one(v1, length(v1));
		//@ assert list(left, ?vl);
		//@ assert list_maximum_common_sublist(vl, tail(v1), v2);
	
		struct list *tr = list_sublist(list2, 1, l2);
		right = list_maximum_common_sublist(list1, tr);
		lr = list_length(right);
		list_dispose(tr);
		//@ take_drop_one(v2, length(v2));
		//@ assert list(right, ?vr);
		//@ assert list_maximum_common_sublist(vr, v1, tail(v2));


	
		middle = list_maximum_common_sublist_0(list1, list2);
		lm = list_length(middle);
		//@ assert list(middle, ?vm);
		//@ assert list_maximum_common_sublist_0(vm, v1, v2);
	
		if (lm >= ll && lm >= lr) {
			result = middle;
			list_dispose(left);
			list_dispose(right);
		} else {
			if (ll >= lr) {
				result = left;
				list_dispose(right);
			} else {
				result = right;
				list_dispose(left);
			}
			list_dispose(middle);
		}
	}
	
	//@ assert list(result, ?vr);
	//@ close list_maximum_common_sublist(vr, v1, v2);
	return result;
}
	

