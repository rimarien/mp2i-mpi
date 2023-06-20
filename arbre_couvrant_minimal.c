typedef double weight_t;
typedef int vertex;

struct edge {
    vertex x;
    vertex y;
    weight_t rho;
};

typedef struct edge edge;

struct graph {
    int n;
    int *degrees;
    edge **adj;
};

typedef struct graph graph_t;

/*fonction number_of_edges prenant un pointeur vers un graphe et renvoyant son
nombre total d’arêtes. Attention à ne compter chaque arête qu’une seule fois, le graphe est
non orienté.*/

int number_of_edges(graph_t *g){
    int p = 0;
    for (vertex x = 0; x < g->n; x++) {
        p += g->degrees[x];
    }
    return p / 2;
}

/*fonction get_edges prenant un pointeur vers un graphe et un pointeur nb_edges
vers un entier, et renvoyant un pointeur vers un bloc alloué contenant toutes les arêtes du
graphe. La fonction aura comme effet secondaire de fixer la valeur pointée par nb_edges
au nombre total d’arêtes du graphe (et donc à la longueur du bloc renvoyé)*/

edge *get_edges(graph_t *g, int *nb_edges){
    int p = number_of_edges(g);
    *nb_edges = p;
    edge *arr = malloc(p * sizeof(edge));
    int next_index = 0;
    for (vertex x = 0; x < g->n; x++) {
        for (int i = 0; i < g->degrees[x]; i++) {
        edge e = g->adj[x][i];
            if (e.x < e.y) {
                arr[next_index] = g->adj[x][i];
                next_index++;
            }
        }
    }
    return arr;
}



int compare_weights(const void *e1, const void *e2){
    weight_t w1 = ((edge*)e1)->rho;
    weight_t w2 = ((edge*)e2)->rho;
    if (w1 < w2) return -1;
    if (w1 > w2) return 1;
    return 0;
}

/*fonction sort_edges qui prend en entrée un tableau d’arêtes et le trie par poids
croissant. On pourra utiliser la fonction qsort de la bibliothèque standard (mais il n’est
pas forcément inutile de ré-écrire votre propre tri rapide, juste pour l’entraînement)*/

void sort_edges(edge *edges, int p){
    qsort(edges, p, sizeof(edge), compare_weights);
}



void swap_edges(edge *arr, int i, int j){
    edge tmp = arr[i];
    arr[i] = arr[j];
    arr[j] = tmp;
}




int partition(edge *arr, int len){
    weight_t w = arr[0].rho;
    int i = 1;
    for (int j = 1; j < len; j++) {
        if (arr[j].rho <= w) {
            swap_edges(arr, i, j);
            i++;
        }
    }
    swap_edges(arr, 0, i - 1);
    return i - 1;
}



void quicksort_edges(edge *arr, int len){
    if (len <= 1) return;
    int pivot = partition(arr, len);
    quicksort_edges(arr, pivot);
    quicksort_edges(arr + pivot + 1, len - pivot - 1);
}

/*fonction print_edge_array qui affiche le contenu d’un tableau d’arêtes. Utiliser
cette fonction pour vérifier sur le graphe fourni en exemple le bon fonctionnement des
get_edges et sort_edges*/

void print_edge_array(edge *edges, int len){
    for (int i = 0; i < len; i++) {
        edge e = edges[i];
        printf("(%d, %d, %.2f)\n", e.x, e.y, e.rho);
    }
    printf("\n");
}

/*fonction partition_new qui crée une partition de [0 . . . n − 1] en singletons*/

partition_t *partition_new(int nb_elements){
    partition_t *p = malloc(sizeof(partition_t));
    p->arr = malloc(nb_elements * sizeof(int));
    p->nb_elements = nb_elements;
    p->nb_sets = nb_elements;
    for (int i = 0; i < nb_elements; i++) {
        p->arr[i] = -1;
    }
    return p;
}

/*fonction partition_free qui libère la mémoire associée à une partition*/

void partition_free(partition_t *p){
    free(p->arr);
    free(p);
}


/*fonction find qui renvoie le représentant de l’entier x passé en argument. Cette
fonction procédera à une compression de chemin*/

int find(partition_t *p, int x){
    if (p->arr[x] < 0) return x;
    int root = find(p, p->arr[x]);
    p->arr[x] = root;
    return root;
}


/*fonction merge qui fusionne les ensembles auxquels appartiennent les deux entiers
passés en argument. Cette fonction effectuera une union par taille*/

void merge(partition_t *p, int x, int y){
    int rx = find(p, x);
    int ry = find(p, y);
    if (rx == ry) return;
    else if (p->arr[rx] <= p->arr[ry]) {
        p->arr[ry] += p->arr[rx];
        p->arr[rx] = ry;
    } else {
        p->arr[rx] += p->arr[ry];
        p->arr[ry] = rx;
    }
    p->nb_sets--;
}


/*Entrées g est un pointeur vers un graphe pondéré non orienté, nb_chosen est un argument
de sortie.
Sortie Un pointeur vers un bloc alloué d’arêtes qui constituent une forêt couvrante minimale de g.
Effet secondaire Après l’appel, la valeur pointée par nb_chosen doit être égale au nombre
d’arêtes choisies.*/

edge *kruskal(graph_t *g, int *nb_chosen){
    int p;
    edge *edges = get_edges(g, &p);
    sort_edges(edges, p);
    partition_t *part = partition_new(g->n);
    edge *mst = malloc((g->n - 1) * sizeof(edge));
    int next_index = 0;
    for (int i = 0; i < p; i++) {
        if (nb_sets(part) == 1) break;
        edge e = edges[i];
        if (find(part, e.x) == find(part, e.y)) continue;
        merge(part, e.x, e.y);
        mst[next_index] = e;
        next_index++;
    }
    free(edges);
    partition_free(part);
    *nb_chosen = next_index;
    return mst;
}



weight_t total_weight(edge *edges, int len){
    float s = 0.;
    for (int i = 0; i < len; i++) {
        s += edges[i].rho;
    }
    return s;
}




int main(void){
    graph_t *g = read_graph(stdin);
    int nb_chosen;
    edge *edges = kruskal(g, &nb_chosen);
    bool connected = (nb_chosen == g->n - 1);
    if (connected) {
        printf("Minimum Spanning Tree:\n");
    } else {
        printf("Minimum Spanning Forest (%d trees):\n", g->n - nb_chosen);
    }
    printf("Total weight %.3f\n", total_weight(edges, nb_chosen));
    print_edge_array(edges, nb_chosen);
    free(edges);
    graph_free(g);
}




void explore(graph_t *g, int *arr, int c, vertex x){
    if (arr[x] != -1) return;
    arr[x] = c;
    for (int i = 0; i < g->degrees[x]; i++) {
        edge e = g->adj[x][i];
        explore(g, arr, c, e.y);
    }
}


/*Entrées Un pointeur g vers un graphe non orienté (et pondéré) G = (V, E); nb_components
est un argument de sortie.
Effets secondaires Après l’appel, la valeur pointée par nb_components vaudra k, le
nombre de composantes connexes de G.
Sortie Un pointeur vers un bloc alloué arr de taille |V|, indiquant pour chaque sommet
le numéro de sa composante connexe. Plus précisément, on exige que :
■ les valeurs contenues dans arr soient dans l’intervalle [0 . . . k − 1];
■ arr[i] soit égal à arr[j] si et seulement si i et j sont dans la même composante
connexe.*/

int *get_components(graph_t *g, int *nb_components){
    int *arr = malloc(g->n * sizeof(int));
    *nb_components = 0;
    for (int i = 0; i < g->n; i++) arr[i] = -1;
    for (vertex x = 0; x < g->n; x++) {
        if (arr[x] == -1) {
            (*nb_components)++;
            explore(g, arr, x, x);
        }
    }
    return arr;
}

/*fonction without_edges qui renvoie un pointeur t vers un graph_t ayant le
même nombre de sommets que le graphe g passé en argument, des blocs t->adj[i] de
même taille que les g->adj[i] mais tous les degrés égaux à zéro (et donc aucune arête)*/

graph_t *without_edges(graph_t *g){
    graph_t *t = malloc(sizeof(graph_t));
    t->n = g->n;
    t->degrees = malloc(t->n * sizeof(int));
    t->adj = malloc(t->n * sizeof(edge*));
    for (int i = 0; i < t->n; i++) {
        t->degrees[i] = 0;
        t->adj[i] = malloc(g->degrees[i] * sizeof(edge));
    }
    return t;
}

/*fonction get_minimal_edge ayant le prototype suivant : Le tableau components et l’entier nb_components indiquent les composantes connexes du
graphe T en cours de construction (qui n’est pas passé en argument), avec les mêmes
conventions que get_components. Cette fonction renvoie un tableau edges de longueur
nb_components tel que edges[c] soit l’arête e de G la plus légère telle que e.x soit dans la
composante numéro c de T et e.y n’y soit pas.*/

edge *get_minimal_edges(graph_t *g, int *components, int nb_components){
    edge *edges = malloc(nb_components * sizeof(edge));
    for (int i = 0; i < nb_components; i++) {
    edge e = {.x = -1, .y = -1, .rho = INFINITY};
    edges[i] = e;
    }
    for (vertex x = 0; x < g->n; x++) {
        for (int i = 0; i < g->degrees[x]; i++) {
            edge e = g->adj[x][i];
            int c = components[x];
            if (components[e.y] != c && e.rho < edges[c].rho) {
                edges[c] = e;
            }
        }
    }
    return edges;
}

/*Entrées Le graphe G pour lequel on cherche à construire un arbre couvrant minimal et le
graphe T correspondant à l’arbre en cours de construction, sous forme de pointeurs vers
des graph_t.
Sortie true si T est connexe, false sinon.
Effets secondaires Si T n’était pas connexe, alors pour chaque composante connexe C de
T, l’arête de poids minimal reliant C à V \ C a été ajoutée à T. Attention, une arête donnée
ne doit être ajoutée qu’une seule fois (et le graphe est non orienté).
On exige une complexité en O(n + p), où n et p sont le nombre de sommets et d’arêtes de
G.*/

bool add_edges(graph_t *g, graph_t *t){
    int nb_components;
    int *components = get_components(t, &nb_components);

    if (nb_components == 1) {
        free(components);
        return true;
    }
    edge *edges = get_minimal_edges(g, components, nb_components);
    
    for (int i = 0; i < nb_components; i++) {
        edge e = edges[i];
        int j = components[e.y];
        // if this edge has already been added when considering the
        // j-th component, ignore it
        if (j < i && components[edges[j].y] == components[e.x]) continue;
        edge e_reverse = {.x = e.y, .y = e.x, .rho = e.rho};
        t->adj[e.x][t->degrees[e.x]] = e;
        t->adj[e.y][t->degrees[e.y]] = e_reverse;
        t->degrees[e.x]++;
        t->degrees[e.y]++;
    }

    free(components);
    free(edges);
    return false;
}

/*fonction boruvka calculant un arbre couvrant minimal du graphe passé en
argument en utilisant l’algorithme de Boruvka*/

graph_t *boruvka(graph_t *g){
    graph_t *t = without_edges(g);
    while (!add_edges(g, t)) {}
    return t;
}
