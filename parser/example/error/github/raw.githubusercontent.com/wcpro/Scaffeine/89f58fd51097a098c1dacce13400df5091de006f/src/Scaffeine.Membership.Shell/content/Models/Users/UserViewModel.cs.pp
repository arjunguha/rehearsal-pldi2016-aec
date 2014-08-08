namespace $rootnamespace$.Models.Users
{
    using System;
    using System.ComponentModel.DataAnnotations;
    using Core.Model;

    [DisplayColumn("Username")]
    public partial class UserViewModel
    {
        [Display(Name = "Full Name", Order = 1)]
        public string FullName
        {
            get { return FirstName + " " + LastName; }
        }

        [Required]
        [Display(Name = "Username", Order = 2)]
        public virtual string Username { get; set; }

        [UIHint("Photo")]
        [Display(Name = "Photo")]
        public string PhotoId { get; set; }

        [Display(Name = "Approved")]
        public virtual bool IsApproved { get; set; }

        [Display(Name = "Last Activity Date")]
        public virtual DateTime? LastActivityDate { get; set; }

        [Display(Name = "Last Login Date")]
        public virtual DateTime? LastLoginDate { get; set; }

        [Display(Name = "Locked Out")]
        public virtual bool IsLockedOut { get; set; }

        [Required]
        [DataType(DataType.EmailAddress)]
        public virtual string Email { get; set; }

        [Display(Name = "First Name")]
        [ScaffoldColumn(false)]
        public virtual string FirstName { get; set; }

        [Display(Name = "Last Name")]
        [ScaffoldColumn(false)]
        public virtual string LastName { get; set; }

        public Gender Gender { get; set; }

        [DataType(DataType.MultilineText)]
        public virtual string Comment { get; set; }
    }
}