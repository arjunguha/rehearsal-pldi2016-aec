using $rootnamespace$.Core.Model;

namespace $rootnamespace$.Models
{
  public enum NotificationType
    {
        info,
        warning,
        success,
        error
    }

    public enum NotificationAction
    {
        created,
        update,
        deleted
    }

    public interface IAlert
    {
        NotificationType NotificationType { get; }
        NotificationAction NotificationAction { get; }
        DomainObject Entity { get; }
        string Message { get; }
    }

    public partial class Alert<T> : IAlert where T: DomainObject
    {
        private readonly T _entity;
        private readonly NotificationType _notificationType;
        private readonly NotificationAction _notificationAction;

        public Alert(T entity, NotificationType notificationType, NotificationAction notificationAction)
        {
            _entity = entity;
            _notificationType = notificationType;
            _notificationAction = notificationAction;
        }

        public string Message
        {
            get
            {
                switch (this.NotificationAction)
                {
                    case NotificationAction.created:
                        return string.Format("{0} was created successfully", _entity.ToString());
                    default:
                        return "";
                }
            }
        }

        public NotificationType NotificationType
        {
            get { return _notificationType; }
        }
    
        public NotificationAction NotificationAction 
        { 
            get { return _notificationAction; }
        }

        public DomainObject Entity
        {
            get { return _entity; }            
        }
    }
}