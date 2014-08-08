using System;
using $rootnamespace$.Models;
using SignalR.Hubs;

namespace $rootnamespace$.Hubs
{
    [HubName("notifications")]
    public partial class NotificationHub : Hub
    {
        public void Notify(UserNotification notification)
        {
            Clients.notify(notification);
        }
    }
}