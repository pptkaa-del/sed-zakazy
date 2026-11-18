FROM node:22-alpine
ENV NODE_ENV=production PORT=3000 DATA_DIR=/data
WORKDIR /app
COPY package.json server.js upr-reports.js ./
COPY upr-templates ./upr-templates
COPY public ./public
# «SSH-консоль» runs the OpenSSH client
RUN apk add --no-cache openssh-client
RUN mkdir -p /data && chown node:node /data
USER node
VOLUME ["/data"]
EXPOSE 3000
HEALTHCHECK --interval=30s --timeout=5s CMD wget -qO- http://127.0.0.1:3000/favicon.svg >/dev/null || exit 1
CMD ["node", "server.js"]
