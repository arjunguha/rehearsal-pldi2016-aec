using $rootnamespace$.Core.Model;

namespace $rootnamespace$.Models
{
    public partial class UserNotification : INotification
    {
        private readonly User _user;
        private readonly string _message;

        public UserNotification(User user, string message)
        {
            _user = user;
            _message = message;
        }

        public string Message { get { return _message; } }
        public User User { get { return _user; } }
    }
}