#ifndef _USER_VDEV_SERIAL_H_
#define _USER_VDEV_SERIAL_H_

#include "../../vmm_dev.h"

struct vserial {
	uint8_t iir;
	int iir_valid;
	struct vdev *vdev;
};

int vserial_init(struct vdev *vdev, struct vserial *dev);

#endif /* !_USER_VDEV_SERIAL_H_ */
