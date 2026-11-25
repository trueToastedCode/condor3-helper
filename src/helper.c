// c3helper.exe - 64-bit data server for the Condor 3 mod (see include/c3h_proto.h, docs/DESIGN.md).
//
// Holds a landscape's complete autogen (Autogen/oXXYY.c3d + textures) in 64-bit memory, cut into chunks with several levels
// of detail, and hands single chunks / textures to the 32-bit game through shared memory. Started by the mod:
//     c3helper.exe --pid <Condor.exe pid> [--log <file>]
// The mod creates the shared objects (Local\c3h_<pid>_*) before starting us; we exit when the game exits or on C3H_REQ_QUIT.
#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdarg.h>
#include "c3h_proto.h"
#define STB_IMAGE_IMPLEMENTATION
#define STBI_ONLY_PNG
#define STBI_NO_STDIO
#include "third_party/stb_image.h"                                // public domain (github.com/nothings/stb)

static FILE* g_log;
static void Log(const char* fmt, ...) {
    va_list ap; SYSTEMTIME t; char line[1024];                       // one fprintf per line: OPEN logs from several threads
    if (!g_log) return;
    GetLocalTime(&t);
    va_start(ap, fmt); _vsnprintf(line, sizeof line - 1, fmt, ap); va_end(ap); line[sizeof line - 1] = 0;
    fprintf(g_log, "%02d:%02d:%02d.%03d %s\n", t.wHour, t.wMinute, t.wSecond, t.wMilliseconds, line); fflush(g_log);
}

// ---- small helpers -------------------------------------------------------------------------------------------
typedef struct { uint8_t* p; size_t n; } Buf;
static Buf ReadFileAll(const char* path) {
    Buf b = {0, 0}; FILE* f = fopen(path, "rb"); long long n;
    if (!f) return b;
    _fseeki64(f, 0, SEEK_END); n = _ftelli64(f); _fseeki64(f, 0, SEEK_SET);
    b.p = (uint8_t*)malloc((size_t)n + 1);
    if (b.p && fread(b.p, 1, (size_t)n, f) == (size_t)n) b.n = (size_t)n; else { free(b.p); b.p = NULL; }
    fclose(f);
    return b;
}
typedef struct { uint8_t* p; size_t n, cap; } Out;
static void* OutAdd(Out* o, const void* src, size_t n) {
    void* dst;
    if (o->n + n > o->cap) { size_t c = o->cap ? o->cap * 2 : 65536; while (c < o->n + n) c *= 2; o->p = (uint8_t*)realloc(o->p, c); o->cap = c; }
    dst = o->p + o->n;
    if (src) memcpy(dst, src, n); else memset(dst, 0, n);
    o->n += n;
    return dst;
}

// ---- C3D -----------------------------------------------------------------------------------------------------
typedef struct { char name[32], tex[260]; uint32_t fv, nv, fi, ni; float color[4], params[3]; } C3dObj;
typedef struct { int nobj; C3dObj* obj; uint32_t nverts, nidx; C3hVertex* v; uint32_t* idx; Buf file; } C3d;

static int ParseC3d(C3d* m, Buf b) {
    size_t o = 3; uint32_t ng, i; const uint8_t* d = b.p;
    memset(m, 0, sizeof *m); m->file = b;
#define NEED(k) do { if (o + (k) > b.n) return 0; } while (0)
    if (b.n < 7 || memcmp(d, "C3D", 3)) return 0;
    NEED(4); memcpy(&ng, d + o, 4); o += 4 + 8 * (size_t)ng;
    NEED(4); memcpy(&i, d + o, 4); o += 4; m->nobj = (int)i;
    m->obj = (C3dObj*)calloc(m->nobj ? m->nobj : 1, sizeof(C3dObj));
    for (i = 0; i < (uint32_t)m->nobj; i++) {
        C3dObj* ob = &m->obj[i]; uint8_t l;
        NEED(1); l = d[o++]; NEED(l); memcpy(ob->name, d + o, l < 31 ? l : 31); o += l;
        NEED(16); memcpy(&ob->fv, d + o, 4); memcpy(&ob->nv, d + o + 4, 4); memcpy(&ob->fi, d + o + 8, 4); memcpy(&ob->ni, d + o + 12, 4); o += 16;
        NEED(1); l = d[o++]; NEED(l); memcpy(ob->tex, d + o, l); o += l;
        NEED(28); memcpy(ob->color, d + o, 16); memcpy(ob->params, d + o + 16, 12); o += 28;
    }
    NEED(4); memcpy(&m->nverts, d + o, 4); o += 4; NEED((size_t)m->nverts * 32); m->v = (C3hVertex*)(d + o); o += (size_t)m->nverts * 32;
    NEED(4); memcpy(&m->nidx, d + o, 4); o += 4; NEED((size_t)m->nidx * 4); m->idx = (uint32_t*)(d + o);
#undef NEED
    for (i = 0; i < (uint32_t)m->nobj; i++) {
        C3dObj* ob = &m->obj[i];
        if (ob->fi + ob->ni > m->nidx) return 0;
    }
    return 1;
}

// ---- landscape state -----------------------------------------------------------------------------------------
// Every chunk has LODS levels. The chain per tile is built from the detail sets the compiler wrote (Autogen/lods.txt: the tile's
// full-detail file first, then coarser sets such as o0201_L19.c3d / o0201_L17.c3d made from the export's own coarser levels), and
// the remaining levels are vertex clustering of the coarsest set. Without lods.txt (older landscapes): full, 8 m, 24 m, 72 m clustering.
// Each level carries a geometric error in metres; the mod picks a chunk's level by how large that error looks on screen.
#define LODS C3H_MAX_LOD
static const int kTexLod[LODS] = { 0, 1, 3, 5 };                // default mip levels dropped per LOD (2048 -> 1024 -> 256 -> 64)

typedef struct { Buf blob[LODS]; } ChunkData;                    // ready-to-send C3hChunk answers
static char       g_dir[MAX_PATH];                                // landscape folder
static uint32_t   g_tx, g_ty, g_cpt = 4;                          // tiles, chunks per tile side
static float      g_tile = 5760.0f;
static C3hChunkInfo* g_info; static ChunkData* g_chunks; static uint32_t g_nchunks;
static char     (*g_tex)[260]; static uint32_t g_ntex;           // texture paths relative to Autogen/
static Buf*       g_texfile;                                      // loaded on demand
static uint8_t  (*g_texDrop)[LODS];                               // mip levels to drop per texture and LOD (0xff = kTexLod):
                                                                  // a detail set's own atlas pages are already coarse -> 0
static CRITICAL_SECTION g_texLock;                                // TexId is called from the OPEN worker threads

// Big landscapes (the native ones: Slovenia3 has 2802 autogen tiles) cannot be cut up at OPEN: that took minutes and GBs, and the
// game showed no autogen meanwhile. Above LAZY_TILES tiles OPEN only lists the tiles: every tile gets a fixed g_cpt x g_cpt grid
// of chunk slots (no adaptive splits), and a tile is read and cut the first time one of its chunks is asked for (the mod asks for
// the nearest first). Slots without triangles answer "empty". Tiles not used for a while are dropped above LAZY_BUDGET.
#define LAZY_TILES   64
#define LAZY_MAX_TEX 4096                                         // texture ids are assigned as tiles are read: upper bound for the mod
#define LAZY_BUDGET  (1536ull << 20)
static int        g_lazy;
static uint8_t*   g_tileState;                                    // 0 = not read, 2 = chunks ready
static DWORD*     g_tileUse;
static uint64_t*  g_tileBytes; static uint64_t g_lazyBytes; static unsigned g_tilesRead, g_tilesDropped;

static int TexId(const char* t, int lod, int drop) {
    uint32_t i; int r = -1;
    if (!t[0]) return -1;
    EnterCriticalSection(&g_texLock);
    if (g_lazy && g_ntex >= LAZY_MAX_TEX) { for (i = 0; i < g_ntex; i++) if (!_stricmp(g_tex[i], t)) { r = (int)i; break; }
                                            if (r < 0) { LeaveCriticalSection(&g_texLock); return -1; } }
    for (i = 0; i < g_ntex; i++) if (!_stricmp(g_tex[i], t)) { r = (int)i; break; }
    if (r < 0) {
        g_tex = realloc(g_tex, (g_ntex + 1) * sizeof *g_tex); strcpy(g_tex[g_ntex], t);
        g_texfile = realloc(g_texfile, (g_ntex + 1) * sizeof *g_texfile); memset(&g_texfile[g_ntex], 0, sizeof(Buf));
        g_texDrop = realloc(g_texDrop, (g_ntex + 1) * sizeof *g_texDrop); memset(g_texDrop[g_ntex], 0xff, LODS);
        r = (int)g_ntex++;
    }
    g_texDrop[r][lod] = (uint8_t)drop;
    LeaveCriticalSection(&g_texLock);
    return r;
}

// open-addressing map uint64 key -> int32 value (vertex clustering)
typedef struct { uint64_t* k; int32_t* v; size_t cap; } Map;
static void MapInit(Map* m, size_t n) { m->cap = 64; while (m->cap < n * 2) m->cap <<= 1; m->k = malloc(m->cap * 8); m->v = malloc(m->cap * 4); memset(m->k, 0xff, m->cap * 8); }
static void MapFree(Map* m) { free(m->k); free(m->v); }
static int32_t* MapSlot(Map* m, uint64_t key, int* isNew) {
    size_t h = (size_t)((key * 0x9E3779B97F4A7C15ull) >> 20) & (m->cap - 1);
    while (m->k[h] != ~0ull && m->k[h] != key) h = (h + 1) & (m->cap - 1);
    *isNew = m->k[h] == ~0ull; m->k[h] = key;
    return &m->v[h];
}

// Builds the answer for one chunk at one LOD from triangle lists per object (tri = index of the first index of a triangle).
// cell 0 = the triangles as they are, else vertex clustering with that cell size (metres).
typedef struct { uint32_t* t; uint32_t n, cap; } TriList;
static void TriAdd(TriList* tl, uint32_t t) { if (tl->n == tl->cap) { tl->cap = tl->cap ? tl->cap * 2 : 256; tl->t = realloc(tl->t, tl->cap * 4); } tl->t[tl->n++] = t; }
static uint32_t BuildChunk(Buf* out, const C3d* m, int tx, int ty, int lod, const TriList* perObj, float cell, int drop, float bmin[3], float bmax[3]) {
    Out o = {0}; C3hChunk* h; uint32_t nparts = 0, nv = 0, ni = 0, tris = 0; int ob;
    C3hPart* parts; Out verts = {0}, idx = {0};
    float uvq = cell > 0 ? 128.0f / cell : 0;                    // texture-coordinate grouping (atlas fraction): 8 m -> 16, 24 m -> 5.3
    if (uvq > 0 && uvq < 2) uvq = 2;
    parts = calloc(m->nobj ? m->nobj : 1, sizeof(C3hPart));
    for (ob = 0; ob < m->nobj; ob++) {
        const TriList* tl = &perObj[ob]; Map map; uint32_t k, firstV = nv, firstI = ni;
        float* acc = NULL; uint32_t nacc = 0, cap = 0;
        if (!tl->n) continue;
        MapInit(&map, (size_t)tl->n * 3);
        for (k = 0; k < tl->n; k++) {
            uint32_t c, out3[3]; int j;
            for (j = 0; j < 3; j++) {
                uint32_t vi = m->idx[tl->t[k] + j]; const C3hVertex* v = &m->v[vi]; uint64_t key; int isNew; int32_t* s;
                if (cell <= 0) key = vi;
                else {
                    int64_t qx = (int64_t)floorf(v->pos[0] / cell) + 4096, qy = (int64_t)floorf(v->pos[1] / cell) + 4096;
                    int64_t qz = (int64_t)floorf(v->pos[2] / cell) + 1024;
                    int64_t qu = (int64_t)floorf(v->uv[0] * uvq) & 255, qv = (int64_t)floorf(v->uv[1] * uvq) & 255;
                    key = ((uint64_t)(qx & 0x3fff) << 42) | ((uint64_t)(qy & 0x3fff) << 28) | ((uint64_t)(qz & 0xfff) << 16) | ((uint64_t)qu << 8) | (uint64_t)qv;
                }
                s = MapSlot(&map, key, &isNew);
                if (isNew) {
                    *s = (int32_t)nacc;
                    if (nacc == cap) { cap = cap ? cap * 2 : 1024; acc = realloc(acc, (size_t)cap * 9 * sizeof(float)); }
                    memset(acc + (size_t)nacc * 9, 0, 9 * sizeof(float)); nacc++;
                }
                {   float* a = acc + (size_t)*s * 9;
                    a[0] += v->pos[0]; a[1] += v->pos[1]; a[2] += v->pos[2]; a[3] += v->normal[0]; a[4] += v->normal[1]; a[5] += v->normal[2];
                    a[6] += v->uv[0]; a[7] += v->uv[1]; a[8] += 1.0f; }
                out3[j] = (uint32_t)*s;
            }
            if (out3[0] == out3[1] || out3[1] == out3[2] || out3[0] == out3[2]) continue;    // collapsed by clustering
            for (c = 0; c < 3; c++) { uint32_t g = firstV + out3[c]; OutAdd(&idx, &g, 4); }
            ni += 3; tris++;
        }
        for (k = 0; k < nacc; k++) {   // cluster averages -> vertices
            float* a = acc + (size_t)k * 9; C3hVertex v; float w = 1.0f / a[8], l;
            v.pos[0] = a[0] * w; v.pos[1] = a[1] * w; v.pos[2] = a[2] * w;
            l = sqrtf(a[3] * a[3] + a[4] * a[4] + a[5] * a[5]); if (l < 1e-6f) { a[3] = 0; a[4] = 0; a[5] = 1; l = 1; }
            v.normal[0] = a[3] / l; v.normal[1] = a[4] / l; v.normal[2] = a[5] / l;
            v.uv[0] = a[6] * w; v.uv[1] = a[7] * w;
            OutAdd(&verts, &v, sizeof v);
            { int q; for (q = 0; q < 3; q++) { if (v.pos[q] < bmin[q]) bmin[q] = v.pos[q]; if (v.pos[q] > bmax[q]) bmax[q] = v.pos[q]; } }
        }
        nv += nacc;
        free(acc); MapFree(&map);
        if (ni == firstI) { nv = firstV; verts.n = (size_t)firstV * sizeof(C3hVertex); continue; }
        {   C3hPart* p = &parts[nparts++]; const C3dObj* so = &m->obj[ob];
            p->first_vertex = firstV; p->vertex_count = nv - firstV; p->first_index = firstI; p->index_count = ni - firstI;
            p->texture = TexId(so->tex, lod, drop); memcpy(p->color, so->color, 16); memcpy(p->params, so->params, 12);
            strncpy(p->name, so->name, 31); }
    }
    if (nparts) {
        h = (C3hChunk*)OutAdd(&o, NULL, sizeof *h);
        h->tile_x = (int16_t)tx; h->tile_y = (int16_t)ty; h->lod = (uint32_t)lod; h->n_parts = nparts; h->n_verts = nv; h->n_indices = ni;
        OutAdd(&o, parts, nparts * sizeof(C3hPart)); OutAdd(&o, verts.p, verts.n); OutAdd(&o, idx.p, idx.n);
    }
    free(parts); free(verts.p); free(idx.p);
    out->p = o.p; out->n = o.n;
    return tris;
}

// Adaptive chunks: a chunk whose full-detail answer would exceed SPLIT_BYTES is cut into four (by triangle centroid), again and
// again up to SPLIT_DEPTH times. Dense photogrammetry (e.g. level-20 exports) otherwise gives 50-150 MB chunks that do not fit the
// arena; they were dropped and the game showed the 8 m LOD up close. Sparse areas keep their big chunks.
// The chunk regions come from the full-detail file; the coarser sets are cut along the same regions (by triangle centroid).
#define SPLIT_BYTES (20u << 20)
#define SPLIT_DEPTH 4                   // base grid g_cpt x g_cpt per tile -> at most (g_cpt << 4)^2 chunks (90 m with g_cpt = 4)
typedef struct { C3hChunkInfo inf; ChunkData cd; int gx, gy, span; TriList* lists0; } Leaf;
typedef struct {
    int tx, ty, nsrc, level[LODS]; char file[LODS][64];            // input: detail sets, finest first (level 0 = unknown)
    const C3d* m; Leaf* leaf; uint32_t nleaf, cap, split;          // output
    uint64_t tris[LODS], bytes[LODS]; uint32_t nobj, nverts, ntris; DWORD ms;
} TileJob;

static void EmitChunk(TileJob* e, TriList* per, float x0, float y0, float size, int depth, int gx, int gy) {
    const C3d* m = e->m; uint64_t ntris = 0; int ob, split; C3hChunkInfo inf; ChunkData cd;
    for (ob = 0; ob < m->nobj; ob++) ntris += per[ob].n;
    if (!ntris) return;
    memset(&inf, 0, sizeof inf); memset(&cd, 0, sizeof cd);
    inf.min[0] = inf.min[1] = inf.min[2] = 1e30f; inf.max[0] = inf.max[1] = inf.max[2] = -1e30f;
    split = !g_lazy && depth < SPLIT_DEPTH && ntris * 44 > SPLIT_BYTES;                    // estimate: 12 B indices + ~1 vertex (32 B) per triangle
    if (!split) {
        inf.tris[0] = BuildChunk(&cd.blob[0], m, e->tx, e->ty, 0, per, 0, 0, inf.min, inf.max);
        split = !g_lazy && depth < SPLIT_DEPTH && cd.blob[0].n > SPLIT_BYTES && ntris > 1;
        if (split) { free(cd.blob[0].p); cd.blob[0].p = NULL; cd.blob[0].n = 0; }
    }
    if (split) {
        float h = size * 0.5f; TriList* kids = calloc((size_t)4 * (m->nobj ? m->nobj : 1), sizeof(TriList)); uint32_t k; int q;
        for (ob = 0; ob < m->nobj; ob++) for (k = 0; k < per[ob].n; k++) {
            uint32_t t = per[ob].t[k]; const float* a = m->v[m->idx[t]].pos; const float* b = m->v[m->idx[t + 1]].pos; const float* c = m->v[m->idx[t + 2]].pos;
            float x = (a[0] + b[0] + c[0]) / 3.0f, y = (a[1] + b[1] + c[1]) / 3.0f;
            q = (x >= x0 + h) * 2 + (y >= y0 + h);
            TriAdd(&kids[(size_t)q * m->nobj + ob], t);
        }
        e->split++;
        for (q = 0; q < 4; q++) EmitChunk(e, &kids[(size_t)q * m->nobj], x0 + (q >> 1) * h, y0 + (q & 1) * h, h, depth + 1, gx * 2 + (q >> 1), gy * 2 + (q & 1));
        for (k = 0; k < (uint32_t)(4 * m->nobj); k++) free(kids[k].t);
        free(kids);
        return;
    }
    if (e->nleaf == e->cap) { e->cap = e->cap ? e->cap * 2 : 32; e->leaf = realloc(e->leaf, e->cap * sizeof *e->leaf); }
    {   Leaf* L = &e->leaf[e->nleaf++];
        L->inf = inf; L->cd = cd; L->span = 1 << (SPLIT_DEPTH - depth);
        L->gx = gx << (SPLIT_DEPTH - depth); L->gy = gy << (SPLIT_DEPTH - depth);   // on the finest grid
        L->lists0 = calloc(m->nobj ? m->nobj : 1, sizeof(TriList));
        for (ob = 0; ob < m->nobj; ob++) if (per[ob].n) {
            L->lists0[ob].t = malloc((size_t)per[ob].n * 4); memcpy(L->lists0[ob].t, per[ob].t, (size_t)per[ob].n * 4);
            L->lists0[ob].n = L->lists0[ob].cap = per[ob].n;
        } }
}

// geometric error (metres) of a source level: ~1/64 of the 3D-tile edge at that level (L20 0.6 m, L19 1.2 m, L17 4.8 m)
static float LevelError(int level) { return level > 0 ? (float)(40075016.7 / (double)(1u << (level > 30 ? 30 : level)) / 64.0) : 0.5f; }

static int LoadC3d(C3d* m, const char* file) {
    char p[MAX_PATH * 2]; Buf f;
    _snprintf(p, sizeof p, "%s\\Autogen\\%s", g_dir, file); f = ReadFileAll(p);
    if (!f.p || !ParseC3d(m, f)) { free(f.p); memset(m, 0, sizeof *m); return 0; }
    return 1;
}

static void ProcessTile(TileJob* J) {
    C3d src[LODS]; int s, l, ob, ci, cj, n = g_cpt, G = (int)g_cpt << SPLIT_DEPTH; uint32_t t, i;
    int srcOf[LODS], dropOf[LODS]; float cellOf[LODS], errOf[LODS]; TriList* lists; TriList* setLists[LODS] = {0}; int32_t* owner; DWORD t0 = GetTickCount();
    memset(src, 0, sizeof src);
    if (!LoadC3d(&src[0], J->file[0])) { Log("tile %d %d: cannot read/parse %s", J->tx, J->ty, J->file[0]); return; }
    for (s = 1; s < J->nsrc; s++) if (!LoadC3d(&src[s], J->file[s])) { Log("tile %d %d: cannot read %s, set ignored", J->tx, J->ty, J->file[s]); J->nsrc = s; break; }
    // the LOD chain: the sets, then clustering of the coarsest set (cell 8 m or 4x the set's error, then x3 per level)
    for (l = 0; l < LODS; l++) {
        if (l < J->nsrc) { srcOf[l] = l; cellOf[l] = 0; errOf[l] = LevelError(J->level[l]); dropOf[l] = 0; }
        else {
            srcOf[l] = J->nsrc - 1; dropOf[l] = 2 * (l - J->nsrc) + 1;           // 1, 3, 5 below the coarsest set
            cellOf[l] = cellOf[l - 1] > 0 ? cellOf[l - 1] * 3.0f : (4.0f * errOf[l - 1] > 8.0f ? 4.0f * errOf[l - 1] : 8.0f);
            errOf[l] = cellOf[l] * 0.5f;
        }
    }
    // full detail: triangle lists per base chunk and object (by centroid), adaptive split -> leaves with LOD 0
    J->m = &src[0];
    lists = calloc((size_t)n * n * (src[0].nobj ? src[0].nobj : 1), sizeof(TriList));
    for (ob = 0; ob < src[0].nobj; ob++) {
        const C3dObj* so = &src[0].obj[ob]; const C3d* m = &src[0];
        for (t = so->fi; t + 2 < so->fi + so->ni; t += 3) {
            const float* a; const float* b; const float* c; float x, y;
            if (m->idx[t] >= m->nverts || m->idx[t + 1] >= m->nverts || m->idx[t + 2] >= m->nverts) continue;
            a = m->v[m->idx[t]].pos; b = m->v[m->idx[t + 1]].pos; c = m->v[m->idx[t + 2]].pos;
            x = (a[0] + b[0] + c[0]) / 3.0f; y = (a[1] + b[1] + c[1]) / 3.0f;
            ci = (int)floorf((x + g_tile * 0.5f) / (g_tile / n)); cj = (int)floorf((y + g_tile * 0.5f) / (g_tile / n));
            if (ci < 0) ci = 0; if (ci >= n) ci = n - 1; if (cj < 0) cj = 0; if (cj >= n) cj = n - 1;
            TriAdd(&lists[((size_t)ci * n + cj) * src[0].nobj + ob], t);
        }
    }
    {   float cs = g_tile / n;
        for (ci = 0; ci < n; ci++) for (cj = 0; cj < n; cj++)
            EmitChunk(J, &lists[((size_t)ci * n + cj) * src[0].nobj], -g_tile * 0.5f + ci * cs, -g_tile * 0.5f + cj * cs, cs, 0, ci, cj);
        for (t = 0; t < (uint32_t)(n * n * src[0].nobj); t++) free(lists[t].t);
        free(lists); }
    // which leaf owns each cell of the finest grid (cells without full detail: the nearest leaf, so coarse triangles there are kept)
    owner = malloc((size_t)G * G * 4);
    for (i = 0; i < (uint32_t)(G * G); i++) owner[i] = -1;
    for (i = 0; i < J->nleaf; i++) { const Leaf* L = &J->leaf[i]; int x, y; for (x = 0; x < L->span; x++) for (y = 0; y < L->span; y++) owner[(L->gx + x) * G + L->gy + y] = (int32_t)i; }
    for (ci = 0; ci < G && J->nleaf; ci++) for (cj = 0; cj < G; cj++) if (owner[ci * G + cj] < 0) {
        float bd = 1e30f; int32_t bi = 0;
        for (i = 0; i < J->nleaf; i++) { const Leaf* L = &J->leaf[i]; float dx = L->gx + L->span * 0.5f - (ci + 0.5f), dy = L->gy + L->span * 0.5f - (cj + 0.5f), d = dx * dx + dy * dy; if (d < bd) { bd = d; bi = (int32_t)i; } }
        owner[ci * G + cj] = -2 - bi;
    }
    // coarser sets: triangle lists per leaf and object
    for (s = 1; s < J->nsrc; s++) {
        const C3d* m = &src[s];
        setLists[s] = calloc((size_t)(J->nleaf ? J->nleaf : 1) * (m->nobj ? m->nobj : 1), sizeof(TriList));
        for (ob = 0; ob < m->nobj && J->nleaf; ob++) {
            const C3dObj* so = &m->obj[ob];
            for (t = so->fi; t + 2 < so->fi + so->ni; t += 3) {
                const float* a; const float* b; const float* c; float x, y; int32_t o;
                if (m->idx[t] >= m->nverts || m->idx[t + 1] >= m->nverts || m->idx[t + 2] >= m->nverts) continue;
                a = m->v[m->idx[t]].pos; b = m->v[m->idx[t + 1]].pos; c = m->v[m->idx[t + 2]].pos;
                x = (a[0] + b[0] + c[0]) / 3.0f; y = (a[1] + b[1] + c[1]) / 3.0f;
                ci = (int)floorf((x + g_tile * 0.5f) / (g_tile / G)); cj = (int)floorf((y + g_tile * 0.5f) / (g_tile / G));
                if (ci < 0) ci = 0; if (ci >= G) ci = G - 1; if (cj < 0) cj = 0; if (cj >= G) cj = G - 1;
                o = owner[ci * G + cj]; if (o < 0) o = -2 - o;
                TriAdd(&setLists[s][(size_t)o * m->nobj + ob], t);
            }
        }
    }
    free(owner);
    // LODs 1.. of every leaf
    for (i = 0; i < J->nleaf; i++) {
        Leaf* L = &J->leaf[i];
        L->inf.err[0] = errOf[0]; L->inf.level[0] = (int8_t)J->level[0];
        for (l = 1; l < LODS; l++) {
            int sidx = srcOf[l]; const TriList* tl = sidx == 0 ? L->lists0 : &setLists[sidx][(size_t)i * src[sidx].nobj];
            L->inf.tris[l] = BuildChunk(&L->cd.blob[l], &src[sidx], J->tx, J->ty, l, tl, cellOf[l], dropOf[l], L->inf.min, L->inf.max);
            L->inf.err[l] = errOf[l]; L->inf.level[l] = (int8_t)(cellOf[l] > 0 ? -1 : J->level[l]);
        }
        for (ob = 0; ob < src[0].nobj; ob++) free(L->lists0[ob].t);
        free(L->lists0); L->lists0 = NULL;
        L->inf.tile_x = (int16_t)J->tx; L->inf.tile_y = (int16_t)J->ty; L->inf.cx = (uint16_t)L->gx; L->inf.cy = (uint16_t)L->gy;
        for (l = 0; l < LODS; l++) {
            L->inf.bytes[l] = (uint32_t)L->cd.blob[l].n; J->tris[l] += L->inf.tris[l]; J->bytes[l] += L->cd.blob[l].n;
            if (L->cd.blob[l].n > C3H_ARENA_SIZE) { Log("chunk %d %d %d %d lod %d too large (%zu bytes), dropped", J->tx, J->ty, L->gx, L->gy, l, L->cd.blob[l].n); free(L->cd.blob[l].p); L->cd.blob[l].p = NULL; L->cd.blob[l].n = 0; L->inf.bytes[l] = 0; }
        }
    }
    for (s = 1; s < J->nsrc; s++) { size_t k; for (k = 0; k < (size_t)(J->nleaf ? J->nleaf : 1) * (src[s].nobj ? src[s].nobj : 1); k++) free(setLists[s][k].t); free(setLists[s]); }
    J->nobj = (uint32_t)src[0].nobj; J->nverts = src[0].nverts; J->ntris = src[0].nidx / 3; J->ms = GetTickCount() - t0;
    for (s = 0; s < J->nsrc; s++) { free(src[s].obj); free(src[s].file.p); }
    {   char ch[160]; int k = 0;
        for (l = 0; l < LODS; l++) k += cellOf[l] > 0 ? _snprintf(ch + k, sizeof ch - k, "%s%.0f m clusters", l ? ", " : "", cellOf[l])
                                                       : _snprintf(ch + k, sizeof ch - k, "%sL%d", l ? ", " : "", J->level[l]);
        Log("tile %d %d: %u objects, %u vertices, %u triangles -> %u chunks (%u splits); LODs %s; %lu ms",
            J->tx, J->ty, J->nobj, J->nverts, J->ntris, J->nleaf, J->split, ch, (unsigned long)J->ms); }
}

static TileJob* g_jobs; static int g_njobs; static volatile LONG g_nextJob;
static DWORD WINAPI TileWorker(LPVOID unused) {
    (void)unused;
    for (;;) { LONG k = InterlockedIncrement(&g_nextJob) - 1; if (k >= g_njobs) return 0; ProcessTile(&g_jobs[k]); }
}

static int OpenLandscape(const char* dir, char* msg) {
    char p[MAX_PATH * 2]; Buf trn, oha, lods; uint32_t w, h; float cell; DWORD t0 = GetTickCount(); int k, nthr, hasSets = 0;
    uint64_t totTris[LODS] = {0}, totBytes[LODS] = {0};
    strncpy(g_dir, dir, sizeof g_dir - 1);
    // a new OPEN replaces everything
    { uint32_t i, l; for (i = 0; i < g_nchunks; i++) for (l = 0; l < LODS; l++) free(g_chunks[i].blob[l].p);
      for (i = 0; i < g_ntex; i++) free(g_texfile[i].p);
      free(g_chunks); free(g_info); free(g_tex); free(g_texfile); free(g_texDrop); g_chunks = NULL; g_info = NULL; g_tex = NULL; g_texfile = NULL; g_texDrop = NULL; g_nchunks = g_ntex = 0;
      free(g_tileState); free(g_tileUse); free(g_tileBytes); g_tileState = NULL; g_tileUse = NULL; g_tileBytes = NULL; g_lazy = 0; g_lazyBytes = 0; g_tilesRead = g_tilesDropped = 0; }
    { const char* nm = strrchr(dir, '\\'); nm = nm ? nm + 1 : dir;
      _snprintf(p, sizeof p, "%s\\%s.trn", dir, nm); trn = ReadFileAll(p);
      if (trn.n < 12) { sprintf(msg, "cannot read %s", p); return -1; }
      memcpy(&w, trn.p, 4); memcpy(&h, trn.p + 4, 4); memcpy(&cell, trn.p + 8, 4); free(trn.p);
      g_tx = w / 64; g_ty = h / 64; g_tile = 64.0f * cell;
      _snprintf(p, sizeof p, "%s\\%s.oha", dir, nm); oha = ReadFileAll(p);
      _snprintf(p, sizeof p, "%s\\Autogen\\lods.txt", dir); lods = ReadFileAll(p); }
    if (!oha.p) { free(lods.p); sprintf(msg, "no .oha: no autogen"); g_nchunks = 0; return 0; }
    oha.p[oha.n] = 0;
    free(g_jobs); g_jobs = NULL; g_njobs = 0;
    {   char* line = strtok((char*)oha.p, "\r\n");
        for (; line; line = strtok(NULL, "\r\n")) {
            int key, tx, ty; char val[64] = ""; TileJob* J;
            if (sscanf(line, "%d %63s", &key, val) < 2 || !val[0]) continue;
            tx = key / 1000; ty = key % 1000;
            g_jobs = realloc(g_jobs, (g_njobs + 1) * sizeof *g_jobs); J = &g_jobs[g_njobs++]; memset(J, 0, sizeof *J);
            J->tx = tx; J->ty = ty; J->nsrc = 1;
            _snprintf(p, sizeof p, "%s\\Autogen\\o%03d%03d.c3d", dir, tx, ty);
            if (GetFileAttributesA(p) != INVALID_FILE_ATTRIBUTES) _snprintf(J->file[0], 64, "o%03d%03d.c3d", tx, ty);
            else _snprintf(J->file[0], 64, "o%02d%02d.c3d", tx, ty);
        }
    }
    free(oha.p);
    if (lods.p) {   // "XXYY level file" (or XXXYYY), finest first per tile; the first entry replaces the default full-detail file
        char* line; lods.p[lods.n] = 0;
        for (line = strtok((char*)lods.p, "\r\n"); line; line = strtok(NULL, "\r\n")) {
            char tile[16], file[64]; int lev, tx, ty, j; size_t tl;
            if (line[0] == '#' || sscanf(line, "%15s %d %63s", tile, &lev, file) != 3) continue;
            tl = strlen(tile);
            if (tl == 4) { tx = (tile[0] - '0') * 10 + tile[1] - '0'; ty = atoi(tile + 2); }
            else if (tl == 6) { tx = (tile[0] - '0') * 100 + (tile[1] - '0') * 10 + tile[2] - '0'; ty = atoi(tile + 3); }
            else continue;
            for (j = 0; j < g_njobs; j++) if (g_jobs[j].tx == tx && g_jobs[j].ty == ty) {
                TileJob* J = &g_jobs[j];
                if (!_stricmp(file, J->file[0])) { J->level[0] = lev; break; }
                if (J->nsrc < LODS) { strncpy(J->file[J->nsrc], file, 63); J->level[J->nsrc] = lev; J->nsrc++; hasSets++; }
                break;
            }
        }
        free(lods.p);
    }
    if (g_njobs > LAZY_TILES) {   // big landscape: slots only, tiles are read on demand (ReadTile)
        uint32_t per = g_cpt * g_cpt, s2; float cs = g_tile / g_cpt;
        g_lazy = 1; g_nchunks = (uint32_t)g_njobs * per;
        g_info = calloc(g_nchunks + 1, sizeof *g_info); g_chunks = calloc(g_nchunks + 1, sizeof *g_chunks);
        g_tileState = calloc((size_t)g_njobs + 1, 1); g_tileUse = calloc((size_t)g_njobs + 1, sizeof *g_tileUse); g_tileBytes = calloc((size_t)g_njobs + 1, sizeof *g_tileBytes);
        for (k = 0; k < g_njobs; k++) for (s2 = 0; s2 < per; s2++) {
            const TileJob* J = &g_jobs[k]; C3hChunkInfo* in = &g_info[(size_t)k * per + s2]; int ci = (int)(s2 / g_cpt), cj = (int)(s2 % g_cpt), l; float cell = 0;
            in->tile_x = (int16_t)J->tx; in->tile_y = (int16_t)J->ty; in->cx = (uint16_t)(ci << SPLIT_DEPTH); in->cy = (uint16_t)(cj << SPLIT_DEPTH);
            in->min[0] = -g_tile * 0.5f + ci * cs; in->min[1] = -g_tile * 0.5f + cj * cs; in->min[2] = -1000.0f;   // height unknown until read
            in->max[0] = in->min[0] + cs; in->max[1] = in->min[1] + cs; in->max[2] = 9000.0f;
            for (l = 0; l < LODS; l++) {                         // the LOD chain ProcessTile will build (sets, then clustering)
                in->bytes[l] = 1;                                // not known yet: "probably there", the answer may be "empty"
                if (l < J->nsrc) { in->level[l] = (int8_t)J->level[l]; in->err[l] = LevelError(J->level[l]); }
                else { cell = cell > 0 ? cell * 3.0f : (4.0f * in->err[l - 1] > 8.0f ? 4.0f * in->err[l - 1] : 8.0f); in->level[l] = -1; in->err[l] = cell * 0.5f; }
            }
        }
        sprintf(msg, "%d tiles: read on demand (%u chunk slots, %d detail sets); %lu ms", g_njobs, g_nchunks, hasSets, (unsigned long)(GetTickCount() - t0));
        return 0;
    }
    {   SYSTEM_INFO si; HANDLE th[8]; GetSystemInfo(&si);
        nthr = (int)si.dwNumberOfProcessors; if (nthr > 4) nthr = 4; if (nthr > g_njobs) nthr = g_njobs; if (nthr < 1) nthr = 1;
        g_nextJob = 0;
        for (k = 0; k < nthr; k++) th[k] = CreateThread(NULL, 0, TileWorker, NULL, 0, NULL);
        WaitForMultipleObjects((DWORD)nthr, th, TRUE, INFINITE);
        for (k = 0; k < nthr; k++) CloseHandle(th[k]); }
    for (k = 0; k < g_njobs; k++) {   // results in tile order
        TileJob* J = &g_jobs[k]; uint32_t i; int l;
        g_info = realloc(g_info, (g_nchunks + J->nleaf + 1) * sizeof *g_info); g_chunks = realloc(g_chunks, (g_nchunks + J->nleaf + 1) * sizeof *g_chunks);
        for (i = 0; i < J->nleaf; i++) { g_info[g_nchunks] = J->leaf[i].inf; g_chunks[g_nchunks] = J->leaf[i].cd; g_nchunks++; }
        for (l = 0; l < LODS; l++) { totTris[l] += J->tris[l]; totBytes[l] += J->bytes[l]; }
        free(J->leaf);
    }
    sprintf(msg, "%u chunks, %u textures, %d detail sets, %d threads; triangles %llu / %llu / %llu / %llu; MB %llu / %llu / %llu / %llu; %lu ms",
            g_nchunks, g_ntex, hasSets, nthr,
            (unsigned long long)totTris[0], (unsigned long long)totTris[1], (unsigned long long)totTris[2], (unsigned long long)totTris[3],
            (unsigned long long)(totBytes[0] >> 20), (unsigned long long)(totBytes[1] >> 20), (unsigned long long)(totBytes[2] >> 20), (unsigned long long)(totBytes[3] >> 20),
            (unsigned long)(GetTickCount() - t0));
    return 0;
}

// Lazy mode: makes sure the tile of chunk slot c is read and cut; drops tiles nobody used for a while above LAZY_BUDGET.
static void ReadTile(uint32_t c) {
    uint32_t per = g_cpt * g_cpt, j = c / per, base = j * per, i, l; TileJob* J = &g_jobs[j]; uint64_t sum = 0; DWORD now = GetTickCount();
    g_tileUse[j] = now;
    if (g_tileState[j] == 2) return;
    J->leaf = NULL; J->nleaf = J->cap = J->split = 0; memset(J->tris, 0, sizeof J->tris); memset(J->bytes, 0, sizeof J->bytes);
    ProcessTile(J);
    for (i = 0; i < per; i++) { C3hChunkInfo* in = &g_info[base + i]; memset(in->bytes, 0, sizeof in->bytes); memset(in->tris, 0, sizeof in->tris); }
    for (i = 0; i < J->nleaf; i++) {
        const Leaf* L = &J->leaf[i]; uint32_t s2 = (uint32_t)(L->gx >> SPLIT_DEPTH) * g_cpt + (uint32_t)(L->gy >> SPLIT_DEPTH);
        if (s2 >= per) { for (l = 0; l < LODS; l++) free(L->cd.blob[l].p); continue; }
        g_info[base + s2] = L->inf; g_chunks[base + s2] = L->cd;
        for (l = 0; l < LODS; l++) sum += L->cd.blob[l].n;
    }
    free(J->leaf); J->leaf = NULL; J->nleaf = J->cap = 0;
    g_tileState[j] = 2; g_tileBytes[j] = sum; g_lazyBytes += sum; g_tilesRead++;
    while (g_lazyBytes > LAZY_BUDGET) {                          // least recently used tile, not touched for 20 s
        int64_t best = -1; DWORD oldest = 0; int k;
        for (k = 0; k < g_njobs; k++) if (g_tileState[k] == 2 && (uint32_t)k != j && now - g_tileUse[k] > 20000 && (best < 0 || now - g_tileUse[k] > oldest)) { best = k; oldest = now - g_tileUse[k]; }
        if (best < 0) break;
        for (i = (uint32_t)best * per; i < ((uint32_t)best + 1) * per; i++) for (l = 0; l < LODS; l++) { free(g_chunks[i].blob[l].p); g_chunks[i].blob[l].p = NULL; g_chunks[i].blob[l].n = 0; }
        g_lazyBytes -= g_tileBytes[best]; g_tileBytes[best] = 0; g_tileState[best] = 0; g_tilesDropped++;
    }
}

// Some native autogen textures are PNG files named .dds (the game's loader takes both). They become an uncompressed 32-bit DDS
// (B8G8R8A8, full mip chain, box filtered) once, in place of the file's bytes.
static int PngToDds(Buf* f) {
    int w, h, comp, mips = 1, m; uint8_t* rgba = stbi_load_from_memory(f->p, (int)f->n, &w, &h, &comp, 4); size_t total = 0, off = 128; uint8_t* d; uint32_t v;
    if (!rgba) return 0;
    while ((w >> (mips - 1)) > 1 || (h >> (mips - 1)) > 1) mips++;
    for (m = 0; m < mips; m++) { int mw = w >> m, mh = h >> m; if (!mw) mw = 1; if (!mh) mh = 1; total += (size_t)mw * mh * 4; }
    d = calloc(128 + total, 1);
    if (!d) { stbi_image_free(rgba); return 0; }
    memcpy(d, "DDS ", 4);
    v = 124; memcpy(d + 4, &v, 4); v = 0x2100F; memcpy(d + 8, &v, 4); memcpy(d + 12, &h, 4); memcpy(d + 16, &w, 4);
    v = (uint32_t)w * 4; memcpy(d + 20, &v, 4); memcpy(d + 28, &mips, 4);
    v = 32; memcpy(d + 76, &v, 4); v = 0x41; memcpy(d + 80, &v, 4); v = 32; memcpy(d + 88, &v, 4);
    v = 0x00ff0000; memcpy(d + 92, &v, 4); v = 0x0000ff00; memcpy(d + 96, &v, 4); v = 0x000000ff; memcpy(d + 100, &v, 4); v = 0xff000000; memcpy(d + 104, &v, 4);
    v = 0x401008; memcpy(d + 108, &v, 4);
    {   size_t i, n = (size_t)w * h; uint8_t* o = d + off;                // level 0: RGBA -> BGRA
        for (i = 0; i < n; i++) { o[i * 4] = rgba[i * 4 + 2]; o[i * 4 + 1] = rgba[i * 4 + 1]; o[i * 4 + 2] = rgba[i * 4]; o[i * 4 + 3] = rgba[i * 4 + 3]; } }
    for (m = 1; m < mips; m++) {                                          // each level: 2x2 box filter of the previous one
        int pw = w >> (m - 1), ph = h >> (m - 1), mw = w >> m, mh = h >> m, x, y, c; const uint8_t* src; uint8_t* dst;
        if (!pw) pw = 1; if (!ph) ph = 1; if (!mw) mw = 1; if (!mh) mh = 1;
        src = d + off; off += (size_t)pw * ph * 4; dst = d + off;
        for (y = 0; y < mh; y++) for (x = 0; x < mw; x++) for (c = 0; c < 4; c++) {
            int x0 = x * 2 < pw ? x * 2 : pw - 1, x1 = x * 2 + 1 < pw ? x * 2 + 1 : pw - 1, y0 = y * 2 < ph ? y * 2 : ph - 1, y1 = y * 2 + 1 < ph ? y * 2 + 1 : ph - 1;
            dst[((size_t)y * mw + x) * 4 + c] = (uint8_t)((src[((size_t)y0 * pw + x0) * 4 + c] + src[((size_t)y0 * pw + x1) * 4 + c] + src[((size_t)y1 * pw + x0) * 4 + c] + src[((size_t)y1 * pw + x1) * 4 + c] + 2) / 4);
        }
    }
    stbi_image_free(rgba);
    free(f->p); f->p = d; f->n = 128 + total;
    return 1;
}

// ---- mip levels for textures that have none ---------------------------------------------------------------------
// About half of the native autogen textures (Slovenia3: 81 of 146 DDS files) are a single level. The game's loader builds the
// mip chain when it loads them; without it distant buildings shimmer and look pixelated. So, once per texture: level 0 decoded,
// 2x2 box filter per level (colour weighted by alpha, so cut-out edges do not turn black), each level encoded again in the
// file's format (simple range fit; BC1 keeps 1-bit alpha). Level 0 stays byte for byte. BC textures get their size rounded up
// to a multiple of 4 (the blocks already cover it; native D3D11 needs it), so every level's block layout is consistent.
typedef struct { uint8_t r, g, b, a; } Px;
static void Rgb565(uint16_t c, Px* p) { p->r = (uint8_t)(((c >> 11) & 31) * 255 / 31); p->g = (uint8_t)(((c >> 5) & 63) * 255 / 63); p->b = (uint8_t)((c & 31) * 255 / 31); p->a = 255; }
static uint16_t To565(float r, float g, float b) {
    int R = (int)(r * 31 / 255 + 0.5f), G = (int)(g * 63 / 255 + 0.5f), B = (int)(b * 31 / 255 + 0.5f);
    R = R < 0 ? 0 : R > 31 ? 31 : R; G = G < 0 ? 0 : G > 63 ? 63 : G; B = B < 0 ? 0 : B > 31 ? 31 : B;
    return (uint16_t)(R << 11 | G << 5 | B);
}
static void ColorPalette(uint16_t c0, uint16_t c1, int four, Px pal[4]) {
    int k; Rgb565(c0, &pal[0]); Rgb565(c1, &pal[1]);
    if (four) for (k = 0; k < 3; k++) { (&pal[2].r)[k] = (uint8_t)((2 * (&pal[0].r)[k] + (&pal[1].r)[k] + 1) / 3); (&pal[3].r)[k] = (uint8_t)(((&pal[0].r)[k] + 2 * (&pal[1].r)[k] + 1) / 3); }
    else { for (k = 0; k < 3; k++) (&pal[2].r)[k] = (uint8_t)(((&pal[0].r)[k] + (&pal[1].r)[k]) / 2); pal[3].r = pal[3].g = pal[3].b = 0; }
    pal[2].a = 255; pal[3].a = four ? 255 : 0;
}
static void DecodeBlock(const uint8_t* b, int bs, int kind, Px out[16]) {          // kind 1 = BC1 (8 bytes), 2 = BC2, 3 = BC3 (16 bytes)
    const uint8_t* c = b + (bs == 16 ? 8 : 0); uint16_t c0 = (uint16_t)(c[0] | c[1] << 8), c1 = (uint16_t)(c[2] | c[3] << 8); Px pal[4]; int i;
    uint32_t idx = (uint32_t)c[4] | (uint32_t)c[5] << 8 | (uint32_t)c[6] << 16 | (uint32_t)c[7] << 24;
    ColorPalette(c0, c1, bs == 16 || c0 > c1, pal);
    for (i = 0; i < 16; i++) out[i] = pal[(idx >> (2 * i)) & 3];
    if (kind == 2) for (i = 0; i < 16; i++) out[i].a = (uint8_t)(((b[i / 2] >> (4 * (i & 1))) & 15) * 17);   // BC2
    else if (kind == 3) {                                                                                              // BC3
        uint8_t a[8]; uint64_t ai = 0; int k;
        a[0] = b[0]; a[1] = b[1];
        if (a[0] > a[1]) for (k = 1; k < 7; k++) a[k + 1] = (uint8_t)(((7 - k) * a[0] + k * a[1] + 3) / 7);
        else { for (k = 1; k < 5; k++) a[k + 1] = (uint8_t)(((5 - k) * a[0] + k * a[1] + 2) / 5); a[6] = 0; a[7] = 255; }
        for (k = 0; k < 6; k++) ai |= (uint64_t)b[2 + k] << (8 * k);
        for (i = 0; i < 16; i++) out[i].a = a[(ai >> (3 * i)) & 7];
    }
}
static void EncodeColor(const Px p[16], uint8_t* o, int allowTransparent) {       // BC1 colour block (BC2/BC3: allowTransparent 0)
    float mean[3] = {0}, ax[3] = {1, 1, 1}, lo = 1e30f, hi = -1e30f; int i, k, n = 0, transp = 0, it; uint16_t c0, c1; Px pal[4]; uint32_t idx = 0;
    for (i = 0; i < 16; i++) { if (allowTransparent && p[i].a < 128) { transp = 1; continue; } for (k = 0; k < 3; k++) mean[k] += (&p[i].r)[k]; n++; }
    if (!n) { o[0] = o[1] = o[2] = o[3] = 0; o[4] = o[5] = o[6] = o[7] = 0xff; return; }   // all transparent
    for (k = 0; k < 3; k++) mean[k] /= n;
    for (it = 0; it < 4; it++) {                                                  // principal axis (power iteration on the covariance)
        float nx[3] = {0}, l;
        for (i = 0; i < 16; i++) { float d[3], dot; if (allowTransparent && p[i].a < 128) continue;
            for (k = 0; k < 3; k++) d[k] = (&p[i].r)[k] - mean[k];
            dot = d[0] * ax[0] + d[1] * ax[1] + d[2] * ax[2]; for (k = 0; k < 3; k++) nx[k] += dot * d[k]; }
        l = sqrtf(nx[0] * nx[0] + nx[1] * nx[1] + nx[2] * nx[2]); if (l < 1e-6f) break;
        for (k = 0; k < 3; k++) ax[k] = nx[k] / l;
    }
    for (i = 0; i < 16; i++) { float t; if (allowTransparent && p[i].a < 128) continue;
        t = ((&p[i].r)[0] - mean[0]) * ax[0] + ((&p[i].r)[1] - mean[1]) * ax[1] + ((&p[i].r)[2] - mean[2]) * ax[2];
        if (t < lo) lo = t; if (t > hi) hi = t; }
    c0 = To565(mean[0] + ax[0] * hi, mean[1] + ax[1] * hi, mean[2] + ax[2] * hi); c1 = To565(mean[0] + ax[0] * lo, mean[1] + ax[1] * lo, mean[2] + ax[2] * lo);
    if (transp) { if (c0 > c1) { uint16_t t = c0; c0 = c1; c1 = t; } }          // 3 colours + transparent: c0 <= c1
    else if (c0 < c1) { uint16_t t = c0; c0 = c1; c1 = t; }                       // 4 colours: c0 > c1 (equal: index 0 everywhere)
    ColorPalette(c0, c1, !transp && c0 > c1, pal);
    for (i = 0; i < 16; i++) {
        int best = 0, bd = 1 << 30, nk = transp ? 3 : 4;
        if (transp && p[i].a < 128) best = 3;
        else for (k = 0; k < nk; k++) { int dr = p[i].r - pal[k].r, dg = p[i].g - pal[k].g, db = p[i].b - pal[k].b, d = dr * dr + dg * dg + db * db; if (d < bd) { bd = d; best = k; } }
        if (!transp && c0 == c1) best = 0;
        idx |= (uint32_t)best << (2 * i);
    }
    o[0] = (uint8_t)c0; o[1] = (uint8_t)(c0 >> 8); o[2] = (uint8_t)c1; o[3] = (uint8_t)(c1 >> 8);
    o[4] = (uint8_t)idx; o[5] = (uint8_t)(idx >> 8); o[6] = (uint8_t)(idx >> 16); o[7] = (uint8_t)(idx >> 24);
}
static void EncodeAlphaBC3(const Px p[16], uint8_t* o) {
    uint8_t lo = 255, hi = 0, a[8]; uint64_t ai = 0; int i, k;
    for (i = 0; i < 16; i++) { if (p[i].a < lo) lo = p[i].a; if (p[i].a > hi) hi = p[i].a; }
    o[0] = hi; o[1] = lo;
    if (hi == lo) { memset(o + 2, 0, 6); return; }
    a[0] = hi; a[1] = lo; for (k = 1; k < 7; k++) a[k + 1] = (uint8_t)(((7 - k) * hi + k * lo + 3) / 7);
    for (i = 0; i < 16; i++) { int best = 0, bd = 1 << 30; for (k = 0; k < 8; k++) { int d = abs(p[i].a - a[k]); if (d < bd) { bd = d; best = k; } } ai |= (uint64_t)best << (3 * i); }
    for (k = 0; k < 6; k++) o[2 + k] = (uint8_t)(ai >> (8 * k));
}
static int GenMips(Buf* f, int* outMips) {
    uint32_t hgt, wid, mips, pf, fourcc, bits, W, H, full = 1, m, v; int bs = 0, kind = 0; size_t total = 0, off = 128, l0; uint8_t* d; Px* img; Px* nxt;
    memcpy(&hgt, f->p + 12, 4); memcpy(&wid, f->p + 16, 4); memcpy(&mips, f->p + 28, 4); memcpy(&pf, f->p + 80, 4); memcpy(&fourcc, f->p + 84, 4); memcpy(&bits, f->p + 88, 4);
    if (mips > 1 || !wid || !hgt) return 0;
    if (pf & 4) { if (fourcc == 0x31545844) { bs = 8; kind = 1; } else if (fourcc == 0x33545844) { bs = 16; kind = 2; } else if (fourcc == 0x35545844) { bs = 16; kind = 3; } else return 0; }
    else if (bits != 32) return 0;
    W = bs ? (wid + 3) & ~3u : wid; H = bs ? (hgt + 3) & ~3u : hgt;
    while ((W >> (full - 1)) > 1 || (H >> (full - 1)) > 1) full++;
    if (full < 2) return 0;
    l0 = bs ? (size_t)(W / 4) * (H / 4) * bs : (size_t)W * H * 4;
    if (128 + l0 > f->n) return 0;
    for (m = 0; m < full; m++) { uint32_t mw = W >> m, mh = H >> m; if (!mw) mw = 1; if (!mh) mh = 1; total += bs ? (size_t)((mw + 3) / 4) * ((mh + 3) / 4) * bs : (size_t)mw * mh * 4; }
    d = malloc(128 + total); img = malloc((size_t)W * H * sizeof(Px)); nxt = malloc((size_t)((W + 1) / 2) * ((H + 1) / 2) * sizeof(Px) + sizeof(Px));
    if (!d || !img || !nxt) { free(d); free(img); free(nxt); return 0; }
    memcpy(d, f->p, 128); memcpy(d + 128, f->p + 128, l0);                  // header, level 0 as it is
    memcpy(d + 12, &H, 4); memcpy(d + 16, &W, 4); memcpy(d + 28, &full, 4);
    v = bs ? (uint32_t)l0 : W * 4; memcpy(d + 20, &v, 4);
    memcpy(&v, d + 8, 4); v |= 0x20000; memcpy(d + 8, &v, 4);                // DDSD_MIPMAPCOUNT
    memcpy(&v, d + 108, 4); v |= 0x401008; memcpy(d + 108, &v, 4);           // complex, texture, mipmap
    if (bs) {                                                                 // decode level 0
        uint32_t bx, by, i;
        for (by = 0; by < H / 4; by++) for (bx = 0; bx < W / 4; bx++) {
            Px blk[16]; DecodeBlock(f->p + 128 + ((size_t)by * (W / 4) + bx) * bs, bs, kind, blk);
            if (kind == 1) for (i = 0; i < 16; i++) if (blk[i].a == 0) blk[i].r = blk[i].g = blk[i].b = 0;
            for (i = 0; i < 16; i++) img[((size_t)by * 4 + i / 4) * W + bx * 4 + i % 4] = blk[i];
        }
    } else { size_t i; const uint8_t* s = f->p + 128; for (i = 0; i < (size_t)W * H; i++) { img[i].b = s[i * 4]; img[i].g = s[i * 4 + 1]; img[i].r = s[i * 4 + 2]; img[i].a = s[i * 4 + 3]; } }
    off = 128 + l0;
    for (m = 1; m < full; m++) {
        uint32_t pw = W >> (m - 1), ph = H >> (m - 1), mw = W >> m, mh = H >> m, x, y; Px* t;
        if (!pw) pw = 1; if (!ph) ph = 1; if (!mw) mw = 1; if (!mh) mh = 1;
        for (y = 0; y < mh; y++) for (x = 0; x < mw; x++) {                   // 2x2 box, colour weighted by alpha
            uint32_t xs[2] = { x * 2 < pw ? x * 2 : pw - 1, x * 2 + 1 < pw ? x * 2 + 1 : pw - 1 }, ys[2] = { y * 2 < ph ? y * 2 : ph - 1, y * 2 + 1 < ph ? y * 2 + 1 : ph - 1 };
            uint32_t sa = 0, sr = 0, sg = 0, sb = 0, ur = 0, ug = 0, ub = 0; int q; Px o;
            for (q = 0; q < 4; q++) { const Px* s = &img[(size_t)ys[q / 2] * pw + xs[q % 2]]; sa += s->a; sr += s->r * s->a; sg += s->g * s->a; sb += s->b * s->a; ur += s->r; ug += s->g; ub += s->b; }
            if (sa) { o.r = (uint8_t)((sr + sa / 2) / sa); o.g = (uint8_t)((sg + sa / 2) / sa); o.b = (uint8_t)((sb + sa / 2) / sa); }
            else { o.r = (uint8_t)((ur + 2) / 4); o.g = (uint8_t)((ug + 2) / 4); o.b = (uint8_t)((ub + 2) / 4); }
            o.a = (uint8_t)((sa + 2) / 4);
            nxt[(size_t)y * mw + x] = o;
        }
        t = img; img = nxt; nxt = t;                                          // (nxt is big enough for every following level)
        if (bs) {
            uint32_t bx, by, nbx = (mw + 3) / 4, nby = (mh + 3) / 4; int i;
            for (by = 0; by < nby; by++) for (bx = 0; bx < nbx; bx++) {
                Px blk[16]; uint8_t* o = d + off + ((size_t)by * nbx + bx) * bs;
                for (i = 0; i < 16; i++) { uint32_t px = bx * 4 + i % 4, py = by * 4 + i / 4; if (px >= mw) px = mw - 1; if (py >= mh) py = mh - 1; blk[i] = img[(size_t)py * mw + px]; }
                if (kind == 1) EncodeColor(blk, o, 1);
                else if (kind == 2) { int k; for (k = 0; k < 8; k++) o[k] = (uint8_t)(((blk[2 * k].a * 15 + 127) / 255) | ((blk[2 * k + 1].a * 15 + 127) / 255) << 4); EncodeColor(blk, o + 8, 0); }
                else { EncodeAlphaBC3(blk, o); EncodeColor(blk, o + 8, 0); }
            }
            off += (size_t)nbx * nby * bs;
        } else { size_t i; uint8_t* o = d + off; for (i = 0; i < (size_t)mw * mh; i++) { o[i * 4] = img[i].b; o[i * 4 + 1] = img[i].g; o[i * 4 + 2] = img[i].r; o[i * 4 + 3] = img[i].a; } off += (size_t)mw * mh * 4; }
    }
    free(img); free(nxt);
    free(f->p); f->p = d; f->n = 128 + total; *outMips = (int)full;
    return 1;
}

// DDS with the first <drop> mip levels removed (DXT1/3/5 or 32-bit uncompressed, no DX10 header).
static size_t MakeTexture(uint8_t* dst, size_t cap, int id, int drop, char* msg) {
    Buf* f; uint32_t hgt, wid, mips, pfFlags, fourcc, bits; size_t off = 128, sz; int bs = 0, i;
    if (id < 0 || (uint32_t)id >= g_ntex) { sprintf(msg, "bad texture id %d", id); return 0; }
    f = &g_texfile[id];
    if (!f->p) {
        char p[MAX_PATH * 2];
        if (!_strnicmp(g_tex[id], "Landscapes\\", 11)) {
            // Texture path relative to the Condor folder ("Landscapes\<name>\Textures\x.dds"), not to Autogen/:
            // the landscape folder is <root>\Landscapes\<name>, so <root> is two levels above it.
            char root[MAX_PATH], * c;
            strncpy(root, g_dir, sizeof root - 1); root[sizeof root - 1] = 0;
            c = strrchr(root, '\\'); if (c) { *c = 0; c = strrchr(root, '\\'); if (c) *c = 0; }
            _snprintf(p, sizeof p, "%s\\%s", root, g_tex[id]);
        } else
            _snprintf(p, sizeof p, "%s\\Autogen\\%s", g_dir, g_tex[id]);
        *f = ReadFileAll(p);
        if (!f->p) { sprintf(msg, "cannot read %s", p); return 0; }
        if (f->n >= 8 && !memcmp(f->p, "\x89PNG", 4)) { if (PngToDds(f)) Log("TEXTURE %d: %s is a PNG, converted to a 32-bit DDS", id, g_tex[id]); }
        else if (f->n >= 128 && !memcmp(f->p, "DDS ", 4)) {
            int nm = 0; DWORD t0 = GetTickCount();
            if (GenMips(f, &nm)) Log("TEXTURE %d: %s had no mip levels: %d generated (%lu ms)", id, g_tex[id], nm, GetTickCount() - t0);
        }
    }
    if (f->n < 128 || memcmp(f->p, "DDS ", 4)) { sprintf(msg, "not a DDS: %s", g_tex[id]); return 0; }
    memcpy(&hgt, f->p + 12, 4); memcpy(&wid, f->p + 16, 4); memcpy(&mips, f->p + 28, 4);
    memcpy(&pfFlags, f->p + 80, 4); memcpy(&fourcc, f->p + 84, 4); memcpy(&bits, f->p + 88, 4);
    if (mips < 1) mips = 1;
    if (pfFlags & 4) { if (fourcc == 0x31545844) bs = 8; else if (fourcc == 0x33545844 || fourcc == 0x35545844) bs = 16; }
    else if (bits != 32) { sprintf(msg, "unsupported DDS format in %s", g_tex[id]); return 0; }
    if (drop >= (int)mips) drop = (int)mips - 1;
    for (i = 0; i < drop; i++) {
        uint32_t w = wid >> i, h = hgt >> i; if (!w) w = 1; if (!h) h = 1;
        off += bs ? (size_t)((w + 3) / 4) * ((h + 3) / 4) * bs : (size_t)w * h * 4;
    }
    if (off > f->n) { sprintf(msg, "truncated DDS %s", g_tex[id]); return 0; }
    sz = 128 + (f->n - off);
    if (sz > cap) { sprintf(msg, "texture too large"); return 0; }
    memcpy(dst, f->p, 128); memcpy(dst + 128, f->p + off, f->n - off);
    {   uint32_t w = wid >> drop, h = hgt >> drop, m = mips - drop, lin; if (!w) w = 1; if (!h) h = 1;
        lin = bs ? ((w + 3) / 4) * ((h + 3) / 4) * bs : w * 4;
        memcpy(dst + 12, &h, 4); memcpy(dst + 16, &w, 4); memcpy(dst + 28, &m, 4); memcpy(dst + 20, &lin, 4); }
    return sz;
}

int main(int argc, char** argv) {
    DWORD pid = 0; char name[64], logp[MAX_PATH] = ""; int i;
    HANDLE map, evReq, evDone, game; C3hHeader* hd; uint8_t* arena;
    for (i = 1; i + 1 < argc; i++) {
        if (!strcmp(argv[i], "--pid")) pid = (DWORD)strtoul(argv[++i], NULL, 10);
        else if (!strcmp(argv[i], "--log")) strncpy(logp, argv[++i], sizeof logp - 1);
    }
    if (logp[0]) g_log = fopen(logp, "w");
    InitializeCriticalSection(&g_texLock);
    Log("c3helper %s, 64-bit=%d, pid arg %lu", __DATE__, (int)(sizeof(void*) == 8), (unsigned long)pid);
    if (!pid) { Log("no --pid"); return 2; }
    _snprintf(name, sizeof name, "Local\\c3h_%lu_shm", (unsigned long)pid);  map = OpenFileMappingA(FILE_MAP_ALL_ACCESS, FALSE, name);
    _snprintf(name, sizeof name, "Local\\c3h_%lu_req", (unsigned long)pid);  evReq = OpenEventA(EVENT_ALL_ACCESS, FALSE, name);
    _snprintf(name, sizeof name, "Local\\c3h_%lu_done", (unsigned long)pid); evDone = OpenEventA(EVENT_ALL_ACCESS, FALSE, name);
    game = OpenProcess(SYNCHRONIZE, FALSE, pid);
    if (!map || !evReq || !evDone) { Log("cannot open shared objects (map %p req %p done %p, err %lu)", map, evReq, evDone, GetLastError()); return 3; }
    hd = (C3hHeader*)MapViewOfFile(map, FILE_MAP_ALL_ACCESS, 0, 0, 0);
    if (!hd || hd->magic != C3H_MAGIC || hd->version != C3H_VERSION) { Log("shared header mismatch (%p)", (void*)hd); return 4; }
    arena = (uint8_t*)hd + hd->header_size;
    hd->helper_ready = 1;
    Log("serving (arena %u MB, game handle %p)", hd->arena_size >> 20, game);
    for (;;) {
        HANDLE hs[2]; DWORD w; int n = 0;
        hs[n++] = evReq; if (game) hs[n++] = game;
        w = WaitForMultipleObjects(n, hs, FALSE, 5000);
        if (w == WAIT_OBJECT_0 + 1) { Log("game exited"); break; }
        if (w != WAIT_OBJECT_0) continue;
        if (hd->done_seq == hd->req_seq) continue;
        hd->status = 0; hd->resp_size = 0; hd->resp_msg[0] = 0;
        switch (hd->req_type) {
        case C3H_REQ_OPEN: {
            char dir[sizeof hd->req_path]; memcpy(dir, hd->req_path, sizeof dir); dir[sizeof dir - 1] = 0;
            Log("OPEN %s", dir);
            hd->status = OpenLandscape(dir, hd->resp_msg);
            if (hd->status == 0) {
                C3hLandscape L; size_t need = sizeof L + (size_t)g_nchunks * sizeof(C3hChunkInfo);
                memset(&L, 0, sizeof L);
                L.tiles_x = g_tx; L.tiles_y = g_ty; L.tile_size = g_tile; L.chunks_per_tile = g_cpt; L.n_chunks = g_nchunks; L.n_textures = g_lazy ? LAZY_MAX_TEX : g_ntex;
                L.n_lods = LODS; L.lod_cell[0] = 0; L.lod_cell[1] = 8; L.lod_cell[2] = 24; L.lod_cell[3] = 72;   // typical (per tile it varies)
                if (need > hd->arena_size) { hd->status = -1; sprintf(hd->resp_msg, "chunk table too large"); }
                else { memcpy(arena, &L, sizeof L); memcpy(arena + sizeof L, g_info, (size_t)g_nchunks * sizeof(C3hChunkInfo)); hd->resp_size = (uint32_t)need; }
            }
            Log("OPEN -> %d: %s", hd->status, hd->resp_msg);
            break; }
        case C3H_REQ_CHUNK: {
            int c = hd->req_arg[0], l = hd->req_arg[1];
            if (c < 0 || (uint32_t)c >= g_nchunks || l < 0 || l >= LODS) { hd->status = -1; sprintf(hd->resp_msg, "bad chunk %d lod %d", c, l); break; }
            if (g_lazy) ReadTile((uint32_t)c);
            if (!g_chunks[c].blob[l].n) { hd->status = 1; break; }
            memcpy(arena, g_chunks[c].blob[l].p, g_chunks[c].blob[l].n); hd->resp_size = (uint32_t)g_chunks[c].blob[l].n;
            break; }
        case C3H_REQ_TEXTURE: {
            int l = hd->req_arg[1]; size_t n;
            if (l < 0) l = 0; if (l >= LODS) l = LODS - 1;
            {   int id = hd->req_arg[0], drop = (id >= 0 && (uint32_t)id < g_ntex && g_texDrop[id][l] != 0xff) ? g_texDrop[id][l] : kTexLod[l];
                n = MakeTexture(arena, hd->arena_size, id, drop, hd->resp_msg); }
            if (!n) { hd->status = -1; Log("TEXTURE %d: %s", hd->req_arg[0], hd->resp_msg); }
            hd->resp_size = (uint32_t)n;
            break; }
        case C3H_REQ_STATS: {
            sprintf(hd->resp_msg, "chunks %u textures %u; lazy %d: tiles read %u dropped %u, %llu MB held", g_nchunks, g_ntex, g_lazy, g_tilesRead, g_tilesDropped, (unsigned long long)(g_lazyBytes >> 20));
            break; }
        case C3H_REQ_QUIT:
            Log("QUIT");
            hd->done_seq = hd->req_seq; SetEvent(evDone);
            return 0;
        default:
            hd->status = -1; sprintf(hd->resp_msg, "unknown request %u", hd->req_type);
        }
        MemoryBarrier();
        hd->done_seq = hd->req_seq;
        SetEvent(evDone);
    }
    hd->helper_ready = 0;
    return 0;
}
