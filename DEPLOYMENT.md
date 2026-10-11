# Forestbrawl - Render Deployment Guide

## Pre-Deployment Checklist

### 1. Environment Variables Setup
Before deploying to Render, set these environment variables in your Render dashboard:

```bash
AUTH_SECRET=<generate-secure-random-string>
PORT=3000
NODE_ENV=production
DATABASE_FILE=/var/data/forestbrawl.db
```

**To generate a secure AUTH_SECRET:**
```bash
openssl rand -base64 32
```

### 2. Repository Setup
```bash
# Make sure you're in the Forestbrawl directory
cd Forestbrawl

# Initialize git if not already done
git init
git add .
git commit -m "Initial Forestbrawl deployment setup"
git remote add origin <your-github-repo-url>
git push -u origin main
```

### 3. Render Dashboard Configuration

1. **Create New Web Service**
   - Connect your GitHub repository
   - Select the repository branch (usually `main`)

2. **Service Configuration**
   - **Name**: `forestbrawl`
   - **Runtime**: Node.js
   - **Region**: Frankfurt (or your preferred region)
   - **Plan**: Free tier or Starter
   - **Build Command**: `npm ci`
   - **Start Command**: `npm start`
   - **Auto-deploy**: Enable (auto-redeploy on git push)

3. **Environment Variables**
   - Add all variables from `.env.example`
   - Use secure values for `AUTH_SECRET`

4. **Persistence (Important!)**
   - Add a Persistent Disk
   - Mount point: `/var/data`
   - Size: 0.5GB (minimum for game data)
   - Set `DATABASE_FILE` to: `/var/data/forestbrawl.db`

### 4. Deployment

**Option A: Manual Deploy from GitHub**
1. Push code to GitHub
2. Render will auto-detect and deploy
3. Check deployment logs in Render dashboard

**Option B: Deploy from Command Line**
```bash
npm start
# Will listen on PORT 3000
```

### 5. Health Check
Render will ping `https://<your-service-url>/api/health` to verify your service is running.

**Response:**
```json
{
  "ok": true,
  "online": 0
}
```

### 6. Accessing Your Game
After deployment:
```
https://<your-service-name>.onrender.com
```

### 7. Custom Domain (Optional)
1. In Render dashboard, go to Settings
2. Click "Add Custom Domain"
3. Point your domain DNS to Render
4. Configure SSL certificate (auto-generated)

## Troubleshooting

### Issue: Service keeps restarting
- Check environment variables are set correctly
- Verify `AUTH_SECRET` is set
- Check logs: `npm start` should not throw errors

### Issue: Game data not persisting
- Verify persistent disk is mounted to `/var/data`
- Ensure `DATABASE_FILE` points to `/var/data/forestbrawl.db`
- Render stores persistent disk data between restarts

### Issue: Players can't connect
- Check Socket.IO configuration in `server.js`
- Verify CORS is properly configured for your domain
- Check Render firewall settings

### View Logs
In Render dashboard:
1. Go to your service
2. Click "Logs" tab
3. See real-time server output

## Performance Tips

1. **Database**: SQLite is initialized automatically on server start. Keep `/var/data/forestbrawl.db` on the persistent VDS/Render disk.

2. **Scaling**: 
   - Free tier: ~10-50 concurrent players
   - Starter tier: ~100-500 concurrent players
   - Standard tier: 1000+ concurrent players

3. **Asset Optimization**:
   - Game assets are already optimized
   - Consider CDN (Cloudflare) for static files

## Security Considerations

1. **Change AUTH_SECRET** - Don't use default value in production
2. **Validate Input** - All player inputs are validated in `server.js`
3. **Rate Limiting** - Consider adding rate limiting for API endpoints
4. **HTTPS** - Render provides free SSL/TLS

## Monitoring

Enable Render's monitoring:
1. View metrics: CPU, Memory, Requests/sec
2. Set up alerts for:
   - Service down
   - High CPU/Memory usage
   - High error rate

## Rollback

If deployment breaks:
1. Go to "Deployment History"
2. Click previous successful deployment
3. Click "Rollback" button
4. Or revert code in GitHub and push

## Support

### VDS Terminal Setup

```bash
cd /path/to/h
node --version  # Must be v22.5.0 or newer
npm ci
cp .env.example .env
nano .env
```

Before starting, set non-empty production values in `.env` for `AUTH_SECRET`, `OWNER_USERNAME`, and `OWNER_PASSWORD`. Set `NODE_ENV=production`, `PORT=3000`, and `DATABASE_FILE` to a writable persistent path. Keep `.env` private and do not commit it. Generate a secret with `openssl rand -hex 32` and paste it into `.env`.

Start or restart the PM2 service:

```bash
pm2 start ecosystem.config.cjs --update-env
pm2 save
```

Check that the Node process responds locally before debugging Nginx:

```bash
curl http://127.0.0.1:3000/api/health
pm2 logs forestbrawl --lines 100
```

If the local health check works but the public domain returns `502`, verify the Nginx upstream points to `http://127.0.0.1:3000` and inspect `pm2 logs forestbrawl` for startup or crash errors. The startup log must contain `listening on 0.0.0.0:3000`.

- Render Docs: https://render.com/docs
- Socket.IO: https://socket.io/docs/
- Node.js: https://nodejs.org/docs/
