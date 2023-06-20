#include <stdlib.h>
#include <stdbool.h>
#include <string.h>
#include <stdio.h>
#include <assert.h>


#define EPS 256
#define ALL 257
#define MATCH 258

#define MAX_LINE_LENGTH 1024
struct state {
    int c;
    struct state *out1;
    struct state *out2;
    int last_set;
};

typedef struct state state_t;

struct nfa {
    state_t *start;
    state_t *final;
    int n;
};

typedef struct nfa nfa_t;

struct stack {
    int length;
    int capacity;
    nfa_t *data;
};

typedef struct stack stack_t;

struct set {
    int length;
    int id;
    state_t **states;
};

typedef struct set set_t;

/*fonction new_state renvoyant un pointeur vers un nouvel état (alloué sur le tas).
Comme dit plus haut, on initialisera last_set à -1.*/

state_t *new_state(int c, state_t *out1, state_t *out2){
    state_t* new_st = malloc(sizeof(state_t));
    new_st->c = c;
    new_st->out1 = out1;
    new_st->out2 = out2;
    new_st->last_set = -1;
    return new_st;
}

/*fonction character qui renvoie un nfa_t reconnaissant le caractère donné. Attention, on renvoie bien un nfa_t, par valeur, et pas un nfa_t*/

nfa_t character(char c){
    state_t* final = new_state(MATCH,NULL,NULL);
    state_t* initial = new_state(c,final,NULL);
    nfa_t automate;
    automate.final = final;
    automate.start = initial;
    automate.n = 2;
    return automate;
}

/*fonction all qui renvoie un nfa_t reconnaissant n’importe quel mot de longueur
1. On utilisera le même automate que pour character, sauf que le champ c de l’état initial
sera mis à la valeur ALL*/

nfa_t all(void){
    nfa_t automate;
    state_t* final = new_state(ALL,NULL,NULL);
    state_t* initial = new_state(MATCH,final,NULL);
    automate.final = final;
    automate.start = initial;
    automate.n = 2;
    return automate;
}

/*fonctions concat, alternative, star et maybe qui correspondent aux différentes
constructions du dernier exercice. Autrement dit, dans l’appel concat(a, b), on suppose
que a et b sont deux automates de Thompson, d’ensembles d’états disjoints, reconnaissant
deux expressions régulières e et f, et l’on demande de renvoyer l’automate de Thompson
pour ef*/

nfa_t concat(nfa_t a, nfa_t b){
    a.final->c = EPS;
    a.final->out1 = b.start;
    a.final = b.final;
    a.n += b.n;
    return a;
}

nfa_t alternative(nfa_t a, nfa_t b){
    nfa_t automate;
    state_t* start = new_state(EPS,a.start,b.start);
    state_t* final = new_state(MATCH,NULL,NULL);
    a.final->c = EPS;
    b.final->c = EPS;
    a.final->out1 = final;
    b.final->out1 = final;
    automate.final = final;
    automate.start = start;
    automate.n = a.n + b.n + 2;
    return automate;
}

nfa_t star(nfa_t a){
    nfa_t automate;
    state_t* start = new_state(EPS,a.start,NULL);
    state_t* final =  new_state(MATCH,NULL,NULL);
    start->out2 = final;
    a.final->c = EPS;
    start->out1 = a.start;
    a.final->out1 = final;
    a.final->out2 = a.start;
    automate.start = start;
    automate.final = final;
    automate.n = a.n + 2;
    return automate;
}

nfa_t maybe(nfa_t a){
    state_t* start = new_state(EPS,a.start,a.final);
    nfa_t automate;
    automate.start = start;
    automate.final = a.final;
    automate.n = a.n + 1;
    return automate;
}

/*Cette fonction renverra true si la lecture du mot s depuis l’état pointé par state nous
amène dans un état final, false sinon. On considérera que le mot s’arrête au premier
caractère nul ou '\n' rencontré, exclu*/

bool backtrack(state_t *state, char *s){
    if (state == NULL) return false;
    if (state->c == EPS) {
        return backtrack(state->out1, s) || backtrack(state->out2, s);
    }
    if (s[0] == '\0' || s[0] == '\n') return state->c == MATCH;
    if (s[0] == state->c || state->c == ALL) {
        return backtrack(state->out1, &s[1]);
    }
    return false;
}

bool accept_backtrack(nfa_t a, char *s){
    return backtrack(a.start, s);
}

void match_stream_backtrack(nfa_t a, FILE *in){
    char *line = malloc((MAX_LINE_LENGTH + 1) * sizeof(char));
    while (true) {
        if (fgets(line, MAX_LINE_LENGTH, in) == NULL) break;
        if (accept_backtrack(a, line)) {
            printf("%s", line);
        }
    }
    free(line);
}


stack_t *stack_new(int capacity){
    stack_t *s = malloc(sizeof(stack_t));
    s->data = malloc(capacity * sizeof(nfa_t));
    s->capacity = capacity;
    s->length = 0;
    return s;
}

void stack_free(stack_t *s){
    free(s->data);
    free(s);
}

nfa_t pop(stack_t *s){
    assert(s->length > 0);
    nfa_t result = s->data[s->length - 1];
    s->length--;
    return result;
}

void push(stack_t *s, nfa_t a){
    assert(s->capacity > s->length);
    s->data[s->length] = a;
    s->length++;
}

nfa_t build(char *regex){
    int size = strlen(regex);
    stack_t* s = stack_new(size);
    for (int i = 0; i < size; i++){
        char c = regex[i];
        nfa_t b;
        nfa_t a;
        switch (c)
        {
        case '@':
            b = pop(s);
            a = pop(s);
            push(s,concat(a,b));
            break;
        case '|':
            b = pop(s);
            a = pop(s);
            push(s,alternative(a,b));
            break;
        case '*':
            a = pop(s);
            push(s,star(a));
            break;
        case '?':
            a = pop(s);
            push(s,maybe(a));
            break;
        case '.':
            push(s,all());
            break;
        default:
            push(s,character(s));
            break;
        }
    }
    assert(s->length = 1);
    nfa_t result = pop(s);
    stack_free(s);
    return result;

}


set_t *empty_set(int capacity, int id){
    state_t **arr = malloc(capacity * sizeof(state_t*));
    set_t *s = malloc(sizeof(set_t));
    s->length = 0;
    s->id = id;
    s->states = arr;
    return s;
}

void set_free(set_t *s){
    free(s->states);
    free(s);
}

/*Préconditions :
■ set est un pointeur valide vers une structure de type set;
■ set.length >= 0;
■ set.states est suffisamment grand pour contenir tous les états ;
■ s est soit le pointeur nul, soit un pointeur vers un état de l’automate de Thompson ;
■ les états présents dans set sont exactement les états x dont le champ last_set est égal
au champ id de set (ce qui peut inclure l’état s).
Postconditions :
■ l’état s a été ajouté à set (s’il n’y était pas déjà) ;
■ tous les états accessibles depuis s en n’utilisant que des ε-transitions l’ont également
été (à nouveau, s’ils n’y étaient pas déjà) ;
■ les champs des différents objets ont été mis à jour pour conserver les invariants.*/


void add_state(set_t *set, state_t *s){
    if (s == NULL || s->last_set == set->id) return;
    s->last_set = set->id;
    set->states[set->length] = s;
    set->length++;
    if (s->c == EPS) {
        add_state(set,s->out1);
        add_state(set,s->out2);
    }
}

/*Préconditions :
■ old_set et new_set sont deux pointeurs valides (et non aliasés) ;
■ les tableaux states des deux ensembles sont suffisamment grands pour recevoir tous
les états nécessaires.
Postconditions :
■ new_set contient l’ensemble des états accessibles depuis les états de old_set en effectuant une transition étiquetée par c, plus éventuellement des ε-transitions ;
■ l’identifiant de new_set est incrémenté de une unité par rapport à celui de old_set (et
le champ last_set a été mis à jour en conséquence dans les états concernés).*/


void step(set_t *old_set, char c, set_t *new_set){
    new_set->id = old_set->id + 1;
    for (int i = 0; i < old_set->length; i++){
        state_t* s = old_set->states[i];
        if (s->c == c || s->c == ALL){
            add_state(new_set,s->out1);
        }
    }
}

/* fonction accept qui prend en entrée un automate et une chaîne, et renvoie true
ou false suivant que le mot (la chaîne) est reconnu ou pas. À nouveau, on considérera que
le mot se termine juste avant le premier caractère '\n ou '\0' rencontré.
*/

bool accept(nfa_t a, char *s, set_t *s1, set_t *s2){
    s1->length = 0;
    add_state(s1, a.start);
    int i = 0;
    while (s[i] != '\0'&& s[i] != '\n') {
        step(s1, s[i], s2);
        set_t *tmp = s1;
        s1 = s2;
        s2 = tmp;
        i++;
    }
    return a.final->last_set == s1->id;
}

/*fonction match_stream ayant le même comportement que
match_stream_backtrack mais utilisant la nouvelle méthode d’exécution de l’automate. On ne créera que deux set_t au total.*/

void match_stream(nfa_t a, FILE *in){
    char line[MAX_LINE_LENGTH + 1];
    set_t *s1 = empty_set(a.n, 0);
    set_t *s2 = empty_set(a.n, 1);
    while (fgets(line, MAX_LINE_LENGTH, in) != NULL) {
        if (accept(a, line, s1, s2)) printf("%s", line);
        s1->id++;
    }
    set_free(s1);
    set_free(s2);
}

int main(int argc, char* argv[]){
    assert(argc >= 2);
    FILE* in_f = stdin;
    if (argc = 3) {
        in_f = fopen(argv[2],"r");
    }
    nfa_t a = build(argv[1]);
    match_stream_backtrack(a,in_f);
    if (argc >= 3 ) fclose(in_f);
    return 0;
}

void free_accessible_states(state_t *q){
    if (q == NULL) return;
    free_accessible(q->out1);
    free_accessible(q->out2);
    free(q);
}

void free_automaton(nfa_t a){
    free_accessible(a.start);
}
